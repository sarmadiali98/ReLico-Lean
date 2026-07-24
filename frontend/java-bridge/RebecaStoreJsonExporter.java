package org.rebecalang.compiler.frontendbridge;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.EnumSet;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import org.rebecalang.compiler.CompilerConfig;
import org.rebecalang.compiler.modelcompiler.RebecaModelCompiler;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.BinaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.BlockStatement;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ConstructorDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.DotPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Expression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.FieldDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.MainDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.MainRebecDefinition;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.MsgsrvDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ParentSuffixPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.RebecaCode;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.RebecaModel;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ReactiveClassDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Statement;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TermPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.VariableDeclarator;
import org.rebecalang.compiler.modelcompiler.timedrebeca.objectmodel.TimedRebecaParentSuffixPrimary;
import org.rebecalang.compiler.utils.CompilerExtension;
import org.rebecalang.compiler.utils.CoreVersion;
import org.rebecalang.compiler.utils.ExceptionContainer;
import org.springframework.context.annotation.AnnotationConfigApplicationContext;

/**
 * Trusted adapter from the existing Timed Rebeca parser AST to the
 * versioned ReLico finite-store JSON bridge.
 *
 * This class performs no Lingua Franca translation.
 */
public final class RebecaStoreJsonExporter {

    private static final int SCHEMA_VERSION = 2;

    private RebecaStoreJsonExporter() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println(
                "usage: RebecaStoreJsonExporter <input.rebeca> <output.json>"
            );
            System.exit(2);
        }

        Path inputPath =
            Path.of(args[0]).toAbsolutePath().normalize();

        Path outputPath =
            Path.of(args[1]).toAbsolutePath().normalize();

        if (!Files.isRegularFile(inputPath)) {
            throw new IllegalArgumentException(
                "input file does not exist: " + inputPath
            );
        }

        try (
            AnnotationConfigApplicationContext context =
                new AnnotationConfigApplicationContext(
                    CompilerConfig.class
                )
        ) {
            RebecaModelCompiler compiler =
                context.getBean(RebecaModelCompiler.class);

            ExceptionContainer exceptions =
                context.getBean(ExceptionContainer.class);

            var compilation =
                compiler.compileRebecaFile(
                    inputPath.toFile(),
                    EnumSet.of(
                        CompilerExtension.TIMED_REBECA
                    ),
                    CoreVersion.CORE_2_1,
                    true
                );

            if (
                compilation == null ||
                !exceptions.exceptionsIsEmpty()
            ) {
                exceptions.print(System.err);

                throw new IllegalArgumentException(
                    "Timed Rebeca parsing or semantic checking failed"
                );
            }

            RebecaModel model =
                compilation.getFirst();

            String json =
                new Exporter(model).render();

            Files.createDirectories(
                Objects.requireNonNull(
                    outputPath.getParent()
                )
            );

            Files.writeString(
                outputPath,
                json,
                StandardCharsets.UTF_8
            );

            System.out.println(
                "Wrote parser bridge JSON: " + outputPath
            );
        }
    }

    private static final class Exporter {

        private final RebecaModel model;

        private Exporter(RebecaModel model) {
            this.model =
                requireNonNull(
                    model,
                    "parser returned a null RebecaModel"
                );
        }

        private String render() {
            RebecaCode code =
                requireNonNull(
                    model.getRebecaCode(),
                    "model has no Rebeca code"
                );

            requireEmpty(
                code.getRecordDeclaration(),
                "record declarations"
            );

            requireEmpty(
                code.getGlobalVariables(),
                "global variables"
            );

            requireEmpty(
                code.getEnvironmentVariables(),
                "environment variables"
            );

            requireEmpty(
                code.getFeatureVariables(),
                "feature variables"
            );

            requireEmpty(
                code.getInterfaceDeclaration(),
                "interface declarations"
            );

            ReactiveClassDeclaration reactiveClass =
                requireOne(
                    code.getReactiveClassDeclaration(),
                    "reactive class"
                );

            validateReactiveClassShape(
                reactiveClass
            );

            String className =
                requireName(
                    reactiveClass.getName(),
                    "reactive class"
                );

            List<VariableDeclarator> stateVariables =
                reactiveClass
                    .getStatevars()
                    .stream()
                    .flatMap(stateField -> {
                        if (
                            stateField.getType() == null ||
                            !"int".equals(
                                stateField
                                    .getType()
                                    .getTypeName()
                            )
                        ) {
                            throw unsupported(
                                "finite-store state variables must have type int"
                            );
                        }

                        return
                            stateField
                                .getVariableDeclarators()
                                .stream();
                    })
                    .collect(Collectors.toList());

            if (stateVariables.isEmpty()) {
                throw unsupported(
                    "expected at least one state variable"
                );
            }

            List<String> stateVariableNames =
                stateVariables
                    .stream()
                    .map(stateVariable -> {
                        String name =
                            requireName(
                                stateVariable.getVariableName(),
                                "state variable"
                            );

                        if (
                            stateVariable
                                .getVariableInitializer() != null
                        ) {
                            throw unsupported(
                                "state-variable declaration initializers"
                            );
                        }

                        return name;
                    })
                    .collect(Collectors.toList());

            if (
                stateVariableNames
                    .stream()
                    .distinct()
                    .count() !=
                stateVariableNames.size()
            ) {
                throw unsupported(
                    "duplicate state-variable names"
                );
            }

            ConstructorDeclaration constructor =
                requireOne(
                    reactiveClass.getConstructors(),
                    "constructor"
                );

            requireEmpty(
                constructor.getFormalParameters(),
                "constructor parameters"
            );

            requireEmpty(
                constructor.getAnnotations(),
                "constructor annotations"
            );

            MsgsrvDeclaration messageServer =
                requireOne(
                    reactiveClass.getMsgsrvs(),
                    "message server"
                );

            requireEmpty(
                messageServer.getFormalParameters(),
                "message-server parameters"
            );

            requireEmpty(
                messageServer.getAnnotations(),
                "message-server annotations"
            );

            String messageServerName =
                requireName(
                    messageServer.getName(),
                    "message server"
                );

            MainDeclaration mainDeclaration =
                requireNonNull(
                    code.getMainDeclaration(),
                    "model has no main declaration"
                );

            MainRebecDefinition actor =
                requireOne(
                    mainDeclaration
                        .getMainRebecDefinition(),
                    "main actor"
                );

            requireEmpty(
                actor.getAnnotations(),
                "main-actor annotations"
            );

            requireEmpty(
                actor.getBindings(),
                "known-rebec bindings"
            );

            requireEmpty(
                actor.getArguments(),
                "constructor arguments"
            );

            String actorName =
                requireName(
                    actor.getName(),
                    "main actor"
                );

            if (actor.getType() == null) {
                throw unsupported(
                    "main actor without a class type"
                );
            }

            String actorClass =
                requireName(
                    actor.getType().getTypeName(),
                    "main actor class"
                );

            if (!className.equals(actorClass)) {
                throw unsupported(
                    "the main actor must instantiate the sole reactive class"
                );
            }

            String constructorBody =
                renderBody(
                    constructor.getBlock(),
                    stateVariableNames,
                    messageServerName,
                    2
                );

            String messageServerBody =
                renderBody(
                    messageServer.getBlock(),
                    stateVariableNames,
                    messageServerName,
                    2
                );

            return
                "{\n" +
                "  \"schemaVersion\": " +
                SCHEMA_VERSION +
                ",\n" +
                "  \"className\": " +
                jsonString(className) +
                ",\n" +
                "  \"actorName\": " +
                jsonString(actorName) +
                ",\n" +
                "  \"actorClass\": " +
                jsonString(actorClass) +
                ",\n" +
                "  \"stateVariables\": " +
                renderStateVariables(
                    stateVariableNames,
                    1
                ) +
                ",\n" +
                "  \"messageServer\": " +
                jsonString(messageServerName) +
                ",\n" +
                "  \"constructorBody\": " +
                constructorBody +
                ",\n" +
                "  \"messageServerBody\": " +
                messageServerBody +
                "\n" +
                "}\n";
        }

        private static void validateReactiveClassShape(
            ReactiveClassDeclaration reactiveClass
        ) {
            requireEmpty(
                reactiveClass.getAnnotations(),
                "reactive-class annotations"
            );

            requireEmpty(
                reactiveClass.getKnownRebecs(),
                "known rebecs"
            );

            requireEmpty(
                reactiveClass.getSynchMethods(),
                "synchronous methods"
            );

            requireEmpty(
                reactiveClass.getImplements(),
                "implemented interfaces"
            );

            if (reactiveClass.getExtends() != null) {
                throw unsupported(
                    "reactive-class inheritance"
                );
            }

            if (reactiveClass.isAbstract()) {
                throw unsupported(
                    "abstract reactive classes"
                );
            }
        }

        private static String renderStateVariables(
            List<String> stateVariables,
            int indent
        ) {
            String prefix =
                spaces(indent);

            String itemPrefix =
                spaces(indent + 1);

            String fieldPrefix =
                spaces(indent + 2);

            List<String> declarations =
                stateVariables
                    .stream()
                    .map(stateVariable ->
                        itemPrefix +
                        "{\n" +
                        fieldPrefix +
                        "\"name\": " +
                        jsonString(stateVariable) +
                        ",\n" +
                        fieldPrefix +
                        "\"initialValue\": 0\n" +
                        itemPrefix +
                        "}"
                    )
                    .collect(Collectors.toList());

            return
                "[\n" +
                String.join(",\n", declarations) +
                "\n" +
                prefix +
                "]";
        }

        private static String renderBody(
            BlockStatement block,
            List<String> stateVariables,
            String messageServer,
            int indent
        ) {
            BlockStatement requiredBlock =
                requireNonNull(
                    block,
                    "method has no block"
                );

            List<String> statements =
                requiredBlock
                    .getStatements()
                    .stream()
                    .map(statement ->
                        renderStatement(
                            statement,
                            stateVariables,
                            messageServer,
                            indent + 1
                        )
                    )
                    .collect(Collectors.toList());

            if (statements.isEmpty()) {
                return "[]";
            }

            String prefix =
                spaces(indent);

            return
                "[\n" +
                String.join(",\n", statements) +
                "\n" +
                prefix +
                "]";
        }

        private static String renderStatement(
            Statement statement,
            List<String> stateVariables,
            String messageServer,
            int indent
        ) {
            if (statement instanceof BinaryExpression binary) {
                return renderAssignment(
                    binary,
                    stateVariables,
                    indent
                );
            }

            if (statement instanceof DotPrimary dotPrimary) {
                return renderSelfSend(
                    dotPrimary,
                    messageServer,
                    indent
                );
            }

            throw unsupported(
                "statement type " +
                statement.getClass().getSimpleName()
            );
        }

        private static String renderAssignment(
            BinaryExpression assignment,
            List<String> stateVariables,
            int indent
        ) {
            if (!"=".equals(assignment.getOperator())) {
                throw unsupported(
                    "binary expression statement with operator " +
                    assignment.getOperator()
                );
            }

            if (
                !(assignment.getLeft()
                    instanceof TermPrimary target)
            ) {
                throw unsupported(
                    "non-variable assignment target"
                );
            }

            if (!stateVariables.contains(target.getName())) {
                throw unsupported(
                    "assignment to undeclared state variable " +
                    target.getName()
                );
            }

            String prefix =
                spaces(indent);

            String fieldPrefix =
                spaces(indent + 1);

            String expression =
                renderExpression(
                    assignment.getRight(),
                    stateVariables,
                    indent + 1
                );

            return
                prefix +
                "{\n" +
                fieldPrefix +
                "\"kind\": \"assign\",\n" +
                fieldPrefix +
                "\"target\": " +
                jsonString(target.getName()) +
                ",\n" +
                fieldPrefix +
                "\"expression\": " +
                expression +
                "\n" +
                prefix +
                "}";
        }

        private static String renderSelfSend(
            DotPrimary dotPrimary,
            String messageServer,
            int indent
        ) {
            if (
                !(dotPrimary.getLeft()
                    instanceof TermPrimary receiver) ||
                !"self".equals(receiver.getName())
            ) {
                throw unsupported(
                    "non-self message send"
                );
            }

            if (
                !(dotPrimary.getRight()
                    instanceof TermPrimary method)
            ) {
                throw unsupported(
                    "message send without a message-server name"
                );
            }

            if (!messageServer.equals(method.getName())) {
                throw unsupported(
                    "self-send to undeclared message server " +
                    method.getName()
                );
            }

            if (!method.getIndices().isEmpty()) {
                throw unsupported(
                    "indexed message-server calls"
                );
            }

            ParentSuffixPrimary suffix =
                method.getParentSuffixPrimary();

            if (
                !(suffix
                    instanceof TimedRebecaParentSuffixPrimary timed)
            ) {
                throw unsupported(
                    "self-send without a Timed Rebeca suffix"
                );
            }

            requireEmpty(
                timed.getArguments(),
                "message arguments"
            );

            if (timed.getAfterExpression() == null) {
                throw unsupported(
                    "self-send without after(...)"
                );
            }

            if (timed.getDeadlineExpression() != null) {
                throw unsupported(
                    "deadline(...)"
                );
            }

            String delay =
                renderNonnegativeIntegerLiteral(
                    timed.getAfterExpression(),
                    "after delay"
                );

            String prefix =
                spaces(indent);

            String fieldPrefix =
                spaces(indent + 1);

            return
                prefix +
                "{\n" +
                fieldPrefix +
                "\"kind\": \"selfSend\",\n" +
                fieldPrefix +
                "\"message\": " +
                jsonString(messageServer) +
                ",\n" +
                fieldPrefix +
                "\"delay\": " +
                delay +
                "\n" +
                prefix +
                "}";
        }

        private static String renderExpression(
            Expression expression,
            List<String> stateVariables,
            int indent
        ) {
            String prefix =
                spaces(indent);

            String fieldPrefix =
                spaces(indent + 1);

            if (expression instanceof Literal literal) {
                String value =
                    renderIntegerLiteral(
                        literal,
                        "integer expression"
                    );

                return
                    "{\n" +
                    fieldPrefix +
                    "\"kind\": \"intLiteral\",\n" +
                    fieldPrefix +
                    "\"value\": " +
                    value +
                    "\n" +
                    prefix +
                    "}";
            }

            if (expression instanceof TermPrimary term) {
                if (
                    term.getParentSuffixPrimary() != null ||
                    !term.getIndices().isEmpty()
                ) {
                    throw unsupported(
                        "function calls or indexed expressions"
                    );
                }

                if (!stateVariables.contains(term.getName())) {
                    throw unsupported(
                        "reference to undeclared variable " +
                        term.getName()
                    );
                }

                return
                    "{\n" +
                    fieldPrefix +
                    "\"kind\": \"stateVar\",\n" +
                    fieldPrefix +
                    "\"name\": " +
                    jsonString(term.getName()) +
                    "\n" +
                    prefix +
                    "}";
            }

            throw unsupported(
                "expression type " +
                expression.getClass().getSimpleName()
            );
        }

        private static String renderNonnegativeIntegerLiteral(
            Expression expression,
            String context
        ) {
            if (!(expression instanceof Literal literal)) {
                throw unsupported(
                    context +
                    " must be an integer literal"
                );
            }

            String value =
                renderIntegerLiteral(
                    literal,
                    context
                );

            if (new BigInteger(value).signum() < 0) {
                throw unsupported(
                    context +
                    " must be nonnegative"
                );
            }

            return value;
        }

        private static String renderIntegerLiteral(
            Literal literal,
            String context
        ) {
            String value =
                requireName(
                    literal.getLiteralValue(),
                    context
                );

            try {
                new BigInteger(value);
            } catch (NumberFormatException exception) {
                throw unsupported(
                    context +
                    " must be an integer literal, received " +
                    value
                );
            }

            return value;
        }
    }

    private static <T> T requireOne(
        List<T> values,
        String description
    ) {
        if (values.size() != 1) {
            throw unsupported(
                "expected exactly one " +
                description +
                ", received " +
                values.size()
            );
        }

        return values.get(0);
    }

    private static void requireEmpty(
        Collection<?> values,
        String description
    ) {
        if (!values.isEmpty()) {
            throw unsupported(
                description
            );
        }
    }

    private static <T> T requireNonNull(
        T value,
        String message
    ) {
        if (value == null) {
            throw unsupported(
                message
            );
        }

        return value;
    }

    private static String requireName(
        String value,
        String description
    ) {
        if (value == null || value.isBlank()) {
            throw unsupported(
                description +
                " has no name"
            );
        }

        return value;
    }

    private static IllegalArgumentException unsupported(
        String construct
    ) {
        return new IllegalArgumentException(
            "unsupported by the ReLico finite-store parser bridge: " +
            construct
        );
    }

    private static String spaces(int count) {
        return "  ".repeat(count);
    }

    private static String jsonString(String value) {
        StringBuilder escaped =
            new StringBuilder();

        escaped.append('"');

        for (int index = 0; index < value.length(); index++) {
            char character =
                value.charAt(index);

            switch (character) {
                case '"' ->
                    escaped.append("\\\"");

                case '\\' ->
                    escaped.append("\\\\");

                case '\b' ->
                    escaped.append("\\b");

                case '\f' ->
                    escaped.append("\\f");

                case '\n' ->
                    escaped.append("\\n");

                case '\r' ->
                    escaped.append("\\r");

                case '\t' ->
                    escaped.append("\\t");

                default -> {
                    if (character < 0x20) {
                        escaped.append(
                            String.format(
                                "\\u%04x",
                                (int) character
                            )
                        );
                    } else {
                        escaped.append(character);
                    }
                }
            }
        }

        escaped.append('"');

        return escaped.toString();
    }
}
