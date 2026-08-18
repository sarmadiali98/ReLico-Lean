package org.rebecalang.compiler.frontendbridge;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import org.rebecalang.compiler.CompilerConfig;
import org.rebecalang.compiler.modelcompiler.RebecaModelCompiler;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Annotation;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.BinaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.BlockStatement;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.CastExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ConditionalStatement;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ConstructorDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.DotPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Expression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.FieldDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ForStatement;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ForInitializer;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.FormalParameterDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Literal;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.MainDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.MainRebecDefinition;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.MsgsrvDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.NonDetExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.OrdinaryPrimitiveType;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.OrdinaryVariableInitializer;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ParentSuffixPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.PlusSubExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.ReactiveClassDeclaration;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.RebecaCode;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.RebecaModel;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Statement;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TermPrimary;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.TernaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.Type;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.UnaryExpression;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.VariableDeclarator;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.VariableInitializer;
import org.rebecalang.compiler.modelcompiler.timedrebeca.objectmodel.TimedRebecaParentSuffixPrimary;
import org.rebecalang.compiler.utils.CompilerExtension;
import org.rebecalang.compiler.utils.CoreVersion;
import org.rebecalang.compiler.utils.ExceptionContainer;
import org.springframework.context.annotation.AnnotationConfigApplicationContext;

/**
 * Trusted adapter from the existing Timed Rebeca parser AST to the
 * ReLico "general" JSON bridge, schema {@code general-v1}.
 *
 * <p>This exporter supersedes the single-class Store and MultiStore
 * exporters. It accepts several reactive classes, several instances
 * including repeated instances of one class, non-empty
 * {@code knownrebecs} with bindings resolved to instance names,
 * constructors with parameters, message-server parameters with their
 * declared types, {@code @priority} at both the instance and the
 * message-server level, the class queue bound, {@code if}/{@code else},
 * {@code for}, and external sends with an optional {@code after}.
 *
 * <p>The exporter performs no Lingua Franca translation, no priority
 * sorting, and no constant folding. It preserves parser declaration
 * order everywhere, because reaction declaration order is semantically
 * load-bearing in the Lingua Franca target: within one reactor, the
 * order in which reactions are declared decides the order in which
 * same-tag reactions fire.
 *
 * <p>Rejections cite the restriction numbers R1-R24 and the deliberate
 * divergences D1-D9 recorded in
 * {@code docs/dtr-fragment/PAPER_FRAGMENT_RESTRICTIONS.md}. That
 * document is the only place the paper's grammar is transcribed; this
 * file does not restate it.
 */
public final class RebecaGeneralJsonExporter {

    /**
     * Emitted in the output as {@code schemaVersion}. Unlike the
     * MultiStore exporter, whose constant was dead because its
     * renderer inlined the number, this constant is the only source of
     * the emitted value.
     */
    private static final int SCHEMA_VERSION = 1;

    private static final String FAMILY = "general";

    private static final String PRIORITY_ANNOTATION = "priority";

    private static final String SELF_REFERENCE = "self";

    private static final String SENDER_REFERENCE = "sender";

    private static final String CLOCK_REFERENCE = "now";

    /**
     * D5. The paper defines no expression language and exhibits only
     * {@code int}, so the value universe is our choice and is recorded
     * as such in the fragment document.
     */
    private static final Set<String> VALUE_TYPES = Set.of(
        "int",
        "boolean"
    );

    private static final Set<String> BINARY_OPERATORS = Set.of(
        "+",
        "-",
        "*",
        "/",
        "%",
        "==",
        "!=",
        "<",
        "<=",
        ">",
        ">=",
        "&&",
        "||"
    );

    private static final Set<String> UNARY_OPERATORS = Set.of(
        "!",
        "-"
    );

    private static final Set<String> BOOLEAN_LITERALS = Set.of(
        "true",
        "false"
    );

    private RebecaGeneralJsonExporter() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println(
                "usage: RebecaGeneralJsonExporter " +
                "<input.rebeca> <output.json>"
            );

            System.exit(2);
        }

        Path inputPath =
            Path.of(args[0]).toAbsolutePath().normalize();

        Path outputPath =
            Path.of(args[1]).toAbsolutePath().normalize();

        if (!Files.isRegularFile(inputPath)) {
            System.err.println(
                "input model is not a regular file: " + inputPath
            );

            System.exit(2);
        }

        try (
            var context =
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
        }
    }

    private static final class Exporter {

        private final RebecaModel model;

        /**
         * Class name to header, in declaration order. A
         * {@link LinkedHashMap} because the emitted class order must
         * match the source order.
         */
        private final Map<String, ClassInfo> classesByName =
            new LinkedHashMap<>();

        /** Instance name to the name of the class it instantiates. */
        private final Map<String, String> instanceClassNames =
            new LinkedHashMap<>();

        private Exporter(RebecaModel model) {
            this.model = model;
        }

        /**
         * Five passes, not two. A class body may send to a class that
         * is declared later in the file, and an instance binding may
         * name an instance declared later in {@code main}, so every
         * name table must be complete before any body is rendered.
         */
        private String render() {
            RebecaCode code =
                requireNonNull(
                    model.getRebecaCode(),
                    "model has no Rebeca code"
                );

            requireEmpty(
                code.getRecordDeclaration(),
                "record declaration"
            );

            requireEmpty(
                code.getGlobalVariables(),
                "global variable block"
            );

            requireEmpty(
                code.getEnvironmentVariables(),
                "environment variable"
            );

            requireEmpty(
                code.getFeatureVariables(),
                "feature variable"
            );

            requireEmpty(
                code.getInterfaceDeclaration(),
                "interface declaration"
            );

            List<ReactiveClassDeclaration> declarations =
                code.getReactiveClassDeclaration();

            if (declarations == null || declarations.isEmpty()) {
                throw unsupported(
                    "a model with no reactive class (R1)"
                );
            }

            MainDeclaration main =
                requireNonNull(
                    code.getMainDeclaration(),
                    "model has no main block"
                );

            collectClassNames(declarations);
            collectClassHeaders(declarations);
            collectInstanceNames(main);

            Json.ObjectBuilder root = Json.object();

            root.put(
                "schemaVersion",
                Json.number(SCHEMA_VERSION)
            );

            root.put("family", Json.text(FAMILY));
            root.put("classes", renderClasses());
            root.put("instances", renderInstances(main));

            return root.build().render(0) + "\n";
        }

        // ----------------------------------------------------------
        // SECTION: collection passes
        // ----------------------------------------------------------

        /**
         * Declared class names, populated by pass one. Needed before
         * pass two because a state variable or a parameter whose type
         * is a class name is a rebec-typed value, which defeats static
         * topology resolution and is rejected as A1 or A2.
         */
        private final Set<String> classNames = new LinkedHashSet<>();

        private record KnownRebec(
            String name,
            String className,
            Integer line
        ) {
        }

        private record StateVariable(
            String name,
            String type,
            Integer line
        ) {
        }

        private record Parameter(
            String name,
            String type,
            Integer line
        ) {
        }

        /**
         * A class header. The constructor and the message servers are
         * kept as raw parser nodes rather than rendered eagerly,
         * because a body may send to a class declared later in the file
         * and so cannot be rendered until every header exists.
         */
        private record ClassInfo(
            String name,
            Integer queueBound,
            Integer line,
            List<KnownRebec> knownRebecs,
            List<StateVariable> stateVariables,
            List<Parameter> constructorParameters,
            ConstructorDeclaration constructor,
            List<MsgsrvDeclaration> messageServers
        ) {

            private KnownRebec knownRebec(String candidate) {
                for (KnownRebec known : knownRebecs) {
                    if (known.name().equals(candidate)) {
                        return known;
                    }
                }

                return null;
            }

            private MsgsrvDeclaration messageServer(String candidate) {
                for (MsgsrvDeclaration server : messageServers) {
                    if (candidate.equals(server.getName())) {
                        return server;
                    }
                }

                return null;
            }

            private boolean hasStateVariable(String candidate) {
                for (StateVariable variable : stateVariables) {
                    if (variable.name().equals(candidate)) {
                        return true;
                    }
                }

                return false;
            }
        }

        /**
         * The name environment of one body. Holds the owning class plus
         * the message-server or constructor parameters and any
         * loop-local counters currently in scope.
         */
        private static final class Scope {

            private final ClassInfo owner;

            private final Set<String> locals = new LinkedHashSet<>();

            private Scope(ClassInfo owner) {
                this.owner = owner;
            }

            private void declare(String name, Integer line) {
                if (
                    SELF_REFERENCE.equals(name) ||
                    SENDER_REFERENCE.equals(name) ||
                    CLOCK_REFERENCE.equals(name)
                ) {
                    throw unsupported(
                        "a declaration of the reserved name " + name +
                        at(line)
                    );
                }

                if (owner.hasStateVariable(name)) {
                    throw unsupported(
                        "a local name shadowing state variable " +
                        name + at(line)
                    );
                }

                if (owner.knownRebec(name) != null) {
                    throw unsupported(
                        "a local name shadowing known rebec " +
                        name + at(line)
                    );
                }

                if (!locals.add(name)) {
                    throw unsupported(
                        "a duplicate local name " + name + at(line)
                    );
                }
            }

            private void undeclare(String name) {
                locals.remove(name);
            }

            private boolean isValue(String name) {
                return locals.contains(name) ||
                    owner.hasStateVariable(name);
            }
        }

        /** Pass one: class names, checked for uniqueness. */
        private void collectClassNames(
            List<ReactiveClassDeclaration> declarations
        ) {
            for (ReactiveClassDeclaration declaration : declarations) {
                requireUnique(
                    classNames,
                    requireName(
                        declaration.getName(),
                        "reactive class"
                    ),
                    "reactive class"
                );
            }
        }

        /** Pass two: class headers, in declaration order. */
        private void collectClassHeaders(
            List<ReactiveClassDeclaration> declarations
        ) {
            for (ReactiveClassDeclaration declaration : declarations) {
                String name = declaration.getName();
                Integer line = declaration.getLineNumber();

                validateClassShape(declaration, name, line);

                List<KnownRebec> knownRebecs =
                    readKnownRebecs(declaration, name);

                List<StateVariable> stateVariables =
                    readStateVariables(declaration, name, knownRebecs);

                ConstructorDeclaration constructor =
                    readConstructor(declaration, name);

                List<Parameter> constructorParameters =
                    constructor == null
                        ? List.of()
                        : readParameters(
                            constructor.getFormalParameters(),
                            "constructor of " + name
                        );

                classesByName.put(
                    name,
                    new ClassInfo(
                        name,
                        readQueueBound(declaration, name, line),
                        line,
                        knownRebecs,
                        stateVariables,
                        constructorParameters,
                        constructor,
                        readMessageServers(declaration, name)
                    )
                );
            }
        }

        private void validateClassShape(
            ReactiveClassDeclaration declaration,
            String name,
            Integer line
        ) {
            requireEmpty(
                declaration.getAnnotations(),
                "an annotation on reactive class " + name + at(line)
            );

            requireEmpty(
                declaration.getSynchMethods(),
                "a synchronized method in " + name +
                " (R11: the fragment has message servers only)" +
                at(line)
            );

            requireEmpty(
                declaration.getImplements(),
                "an interface implementation in " + name +
                " (R12)" + at(line)
            );

            if (declaration.getExtends() != null) {
                throw unsupported(
                    "reactive-class inheritance in " + name +
                    " (R12)" + at(line)
                );
            }

            Boolean isAbstract = declaration.isAbstract();

            if (isAbstract != null && isAbstract) {
                throw unsupported(
                    "an abstract reactive class " + name +
                    " (R12)" + at(line)
                );
            }
        }

        /**
         * R7. The bound is mandatory syntax. The paper gives it no
         * semantics, which is filed as a correction, but a frontend
         * cannot invent one either, so it is carried through verbatim
         * for the downstream well-formedness check to interpret.
         */
        private Integer readQueueBound(
            ReactiveClassDeclaration declaration,
            String name,
            Integer line
        ) {
            Integer bound = declaration.getQueueSize();

            if (bound == null) {
                throw unsupported(
                    "reactive class " + name +
                    " without a queue bound (R7)" + at(line)
                );
            }

            if (bound < 1) {
                throw unsupported(
                    "a queue bound below one in " + name +
                    at(line)
                );
            }

            return bound;
        }

        /**
         * D1. Fig. 4 admits exactly one type group with at least one
         * name; we accept zero or more groups, because the paper's own
         * Fig. 1a and Fig. 2a declare an empty block and because real
         * models need known rebecs of several classes.
         */
        private List<KnownRebec> readKnownRebecs(
            ReactiveClassDeclaration declaration,
            String owner
        ) {
            List<KnownRebec> collected = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();

            List<FieldDeclaration> groups =
                declaration.getKnownRebecs();

            if (groups == null) {
                return List.of();
            }

            for (FieldDeclaration group : groups) {
                String className =
                    typeName(
                        group.getType(),
                        "known rebec group in " + owner,
                        group.getLineNumber()
                    );

                if (!classNames.contains(className)) {
                    throw unsupported(
                        "a known rebec of non-actor type " +
                        className + " in " + owner +
                        at(group.getLineNumber())
                    );
                }

                for (
                    VariableDeclarator declarator :
                        declarators(group, "known rebec", owner)
                ) {
                    Integer line = declarator.getLineNumber() == null
                        ? group.getLineNumber()
                        : declarator.getLineNumber();

                    String name =
                        requireName(
                            declarator.getVariableName(),
                            "known rebec in " + owner
                        );

                    if (declarator.getVariableInitializer() != null) {
                        throw unsupported(
                            "an initialized known rebec " + name +
                            " in " + owner +
                            " (bindings belong in main, R5)" + at(line)
                        );
                    }

                    requireUnique(
                        seen,
                        name,
                        "known rebec in " + owner
                    );

                    collected.add(
                        new KnownRebec(name, className, line)
                    );
                }
            }

            return List.copyOf(collected);
        }

        /**
         * D2. Fig. 4 makes the block mandatory, but Fig. 2a's
         * Controller has none, so absence is accepted.
         */
        private List<StateVariable> readStateVariables(
            ReactiveClassDeclaration declaration,
            String owner,
            List<KnownRebec> knownRebecs
        ) {
            List<StateVariable> collected = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();

            for (KnownRebec known : knownRebecs) {
                seen.add(known.name());
            }

            List<FieldDeclaration> groups = declaration.getStatevars();

            if (groups == null) {
                return List.of();
            }

            for (FieldDeclaration group : groups) {
                String type =
                    typeName(
                        group.getType(),
                        "state variable group in " + owner,
                        group.getLineNumber()
                    );

                if (classNames.contains(type)) {
                    throw unsupported(
                        "A1: a rebec-typed state variable of type " +
                        type + " in " + owner +
                        ", which makes the sender set of a message " +
                        "server statically uncomputable" +
                        at(group.getLineNumber())
                    );
                }

                if (!VALUE_TYPES.contains(type)) {
                    throw unsupported(
                        "a state variable of type " + type +
                        " in " + owner + " (D5 admits " +
                        String.join(", ", VALUE_TYPES) + ")" +
                        at(group.getLineNumber())
                    );
                }

                for (
                    VariableDeclarator declarator :
                        declarators(group, "state variable", owner)
                ) {
                    Integer line = declarator.getLineNumber() == null
                        ? group.getLineNumber()
                        : declarator.getLineNumber();

                    String name =
                        requireName(
                            declarator.getVariableName(),
                            "state variable in " + owner
                        );

                    if (declarator.getVariableInitializer() != null) {
                        throw unsupported(
                            "an initialized state variable " + name +
                            " in " + owner +
                            " (Fig. 4 VarDecl admits no initializer; " +
                            "initialize in the constructor)" + at(line)
                        );
                    }

                    requireUnique(
                        seen,
                        name,
                        "member name in " + owner
                    );

                    collected.add(
                        new StateVariable(name, type, line)
                    );
                }
            }

            return List.copyOf(collected);
        }

        private List<VariableDeclarator> declarators(
            FieldDeclaration group,
            String description,
            String owner
        ) {
            List<VariableDeclarator> declarators =
                group.getVariableDeclarators();

            if (declarators == null || declarators.isEmpty()) {
                throw unsupported(
                    "a " + description + " group declaring no name in " +
                    owner + at(group.getLineNumber())
                );
            }

            return declarators;
        }

        /** R10. At most one constructor, named for its class. */
        private ConstructorDeclaration readConstructor(
            ReactiveClassDeclaration declaration,
            String owner
        ) {
            List<ConstructorDeclaration> constructors =
                declaration.getConstructors();

            if (constructors == null || constructors.isEmpty()) {
                return null;
            }

            if (constructors.size() > 1) {
                throw unsupported(
                    "constructor overloading in " + owner +
                    " (R10 admits at most one)" +
                    at(constructors.get(1).getLineNumber())
                );
            }

            ConstructorDeclaration constructor = constructors.get(0);

            if (!owner.equals(constructor.getName())) {
                throw unsupported(
                    "a constructor named " + constructor.getName() +
                    " in class " + owner + " (R10)" +
                    at(constructor.getLineNumber())
                );
            }

            return constructor;
        }

        private List<MsgsrvDeclaration> readMessageServers(
            ReactiveClassDeclaration declaration,
            String owner
        ) {
            List<MsgsrvDeclaration> servers = declaration.getMsgsrvs();

            if (servers == null) {
                return List.of();
            }

            Set<String> seen = new LinkedHashSet<>();

            for (MsgsrvDeclaration server : servers) {
                requireUnique(
                    seen,
                    requireName(
                        server.getName(),
                        "message server in " + owner
                    ),
                    "message server in " + owner
                );

                Boolean isAbstract = server.isAbstract();

                if (isAbstract != null && isAbstract) {
                    throw unsupported(
                        "an abstract message server " +
                        server.getName() + " in " + owner +
                        at(server.getLineNumber())
                    );
                }

                readParameters(
                    server.getFormalParameters(),
                    "message server " + owner + "." + server.getName()
                );
            }

            return servers;
        }

        /**
         * Message-server and constructor parameters with their declared
         * types. No previous exporter read these at all, so payload
         * types reach the Lean side for the first time here.
         */
        private List<Parameter> readParameters(
            List<FormalParameterDeclaration> parameters,
            String owner
        ) {
            if (parameters == null || parameters.isEmpty()) {
                return List.of();
            }

            List<Parameter> collected = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();

            for (FormalParameterDeclaration parameter : parameters) {
                Integer line = parameter.getLineNumber();

                String name =
                    requireName(
                        parameter.getName(),
                        "parameter of " + owner
                    );

                String type =
                    typeName(
                        parameter.getType(),
                        "parameter " + name + " of " + owner,
                        line
                    );

                if (classNames.contains(type)) {
                    throw unsupported(
                        "A2: a rebec-typed parameter " + name +
                        " of type " + type + " in " + owner +
                        ", which makes the topology dynamic" + at(line)
                    );
                }

                if (!VALUE_TYPES.contains(type)) {
                    throw unsupported(
                        "a parameter " + name + " of type " + type +
                        " in " + owner + " (D5 admits " +
                        String.join(", ", VALUE_TYPES) + ")" + at(line)
                    );
                }

                requireUnique(seen, name, "parameter of " + owner);
                collected.add(new Parameter(name, type, line));
            }

            return List.copyOf(collected);
        }

        /**
         * Pass three: instance name to class name. Complete before any
         * binding is resolved, because a binding may name an instance
         * declared later in main.
         */
        private void collectInstanceNames(MainDeclaration main) {
            List<MainRebecDefinition> definitions =
                main.getMainRebecDefinition();

            if (definitions == null || definitions.isEmpty()) {
                throw unsupported(
                    "an empty main block: Fig. 4 writes " +
                    "InstanceDecl* but Fig. 5 writes InstDecl+, and a " +
                    "model with no actor has no behaviour to translate" +
                    at(main.getLineNumber())
                );
            }

            Set<String> seen = new LinkedHashSet<>();

            for (MainRebecDefinition definition : definitions) {
                Integer line = definition.getLineNumber();

                String name =
                    requireName(definition.getName(), "instance");

                requireUnique(seen, name, "instance");

                String className =
                    typeName(
                        definition.getType(),
                        "instance " + name,
                        line
                    );

                if (!classesByName.containsKey(className)) {
                    throw unsupported(
                        "an instance " + name +
                        " of undeclared reactive class " + className +
                        at(line)
                    );
                }

                instanceClassNames.put(name, className);
            }
        }

        /**
         * The parser resolves a simple type to an
         * {@link OrdinaryPrimitiveType} whose type name is the written
         * name; anything else surfaces as the sentinel
         * {@code General-Type} and is rejected rather than guessed at.
         */
        private static String typeName(
            Type type,
            String description,
            Integer line
        ) {
            Type resolved =
                requireNonNull(
                    type,
                    description + " has no type" + at(line)
                );

            String name = resolved.getTypeName();

            if (
                name == null ||
                name.isBlank() ||
                "General-Type".equals(name)
            ) {
                throw unsupported(
                    "a " + description +
                    " whose type the parser did not resolve to a " +
                    "simple name" + at(line)
                );
            }

            return name;
        }

        /**
         * R6. One non-negative integer literal, at most one annotation,
         * and the identifier must be {@code priority}. Returns null
         * when absent; the contention rule that decides whether absence
         * is fatal lives downstream, not here, because it depends on
         * the whole topology.
         */
        private static String extractPriority(
            List<Annotation> annotations,
            String description
        ) {
            if (annotations == null || annotations.isEmpty()) {
                return null;
            }

            String priority = null;

            for (Annotation annotation : annotations) {
                Integer line = annotation.getLineNumber();

                if (
                    !PRIORITY_ANNOTATION.equals(
                        annotation.getIdentifier()
                    )
                ) {
                    throw unsupported(
                        "annotation @" + annotation.getIdentifier() +
                        " on " + description +
                        " (R6 admits @priority only)" + at(line)
                    );
                }

                if (priority != null) {
                    throw unsupported(
                        "a duplicate @priority on " + description +
                        at(line)
                    );
                }

                if (
                    !(annotation.getValue() instanceof Literal literal)
                ) {
                    throw unsupported(
                        "a non-literal @priority argument on " +
                        description + " (R6)" + at(line)
                    );
                }

                priority =
                    integerLiteralText(
                        literal.getLiteralValue(),
                        "@priority argument on " + description,
                        line
                    );
            }

            return priority;
        }

        private static String integerLiteralText(
            String text,
            String description,
            Integer line
        ) {
            String value =
                requireNonNull(
                    text,
                    description + " has no literal value" + at(line)
                ).trim();

            BigInteger parsed;

            try {
                parsed = new BigInteger(value);
            } catch (NumberFormatException cause) {
                throw unsupported(
                    "a non-integer " + description + " " + value +
                    at(line)
                );
            }

            if (parsed.signum() < 0) {
                throw unsupported(
                    "a negative " + description + " " + value + at(line)
                );
            }

            return parsed.toString();
        }

        // ----------------------------------------------------------
        // SECTION: class and instance rendering
        // ----------------------------------------------------------

        /** Pass four: class bodies, in declaration order. */
        private Json renderClasses() {
            Json.ArrayBuilder classes = Json.array();

            for (ClassInfo info : classesByName.values()) {
                classes.add(renderClass(info));
            }

            return classes.build();
        }

        private Json renderClass(ClassInfo info) {
            Json.ArrayBuilder knownRebecs = Json.array();

            for (KnownRebec known : info.knownRebecs()) {
                knownRebecs.add(
                    Json.object()
                        .put("name", Json.text(known.name()))
                        .put("className", Json.text(known.className()))
                        .put("line", renderLine(known.line()))
                        .build()
                );
            }

            Json.ArrayBuilder stateVariables = Json.array();

            for (StateVariable variable : info.stateVariables()) {
                stateVariables.add(
                    Json.object()
                        .put("name", Json.text(variable.name()))
                        .put("type", Json.text(variable.type()))
                        .put("line", renderLine(variable.line()))
                        .build()
                );
            }

            return Json.object()
                .put("name", Json.text(info.name()))
                .put("queueBound", Json.number(info.queueBound()))
                .put("line", renderLine(info.line()))
                .put("knownRebecs", knownRebecs.build())
                .put("stateVariables", stateVariables.build())
                .put("constructor", renderConstructor(info))
                .put("messageServers", renderMessageServers(info))
                .build();
        }

        private Json renderConstructor(ClassInfo info) {
            ConstructorDeclaration constructor = info.constructor();

            if (constructor == null) {
                return Json.nullValue();
            }

            String description = "constructor of " + info.name();

            requireEmpty(
                constructor.getAnnotations(),
                "an annotation on the " + description +
                " (Fig. 4 gives Constructor no Priority)" +
                at(constructor.getLineNumber())
            );

            Scope scope = new Scope(info);

            declareParameters(scope, info.constructorParameters());

            return Json.object()
                .put("line", renderLine(constructor.getLineNumber()))
                .put(
                    "parameters",
                    renderParameters(info.constructorParameters())
                )
                .put(
                    "body",
                    renderBody(
                        constructor.getBlock(),
                        scope,
                        description
                    )
                )
                .build();
        }

        private Json renderMessageServers(ClassInfo info) {
            Json.ArrayBuilder servers = Json.array();

            for (MsgsrvDeclaration server : info.messageServers()) {
                String description =
                    "message server " + info.name() + "." +
                    server.getName();

                List<Parameter> parameters =
                    readParameters(
                        server.getFormalParameters(),
                        description
                    );

                Scope scope = new Scope(info);
                declareParameters(scope, parameters);

                String priority =
                    extractPriority(
                        server.getAnnotations(),
                        description
                    );

                servers.add(
                    Json.object()
                        .put("name", Json.text(server.getName()))
                        .put("priority", renderPriority(priority))
                        .put(
                            "line",
                            renderLine(server.getLineNumber())
                        )
                        .put(
                            "parameters",
                            renderParameters(parameters)
                        )
                        .put(
                            "body",
                            renderBody(
                                server.getBlock(),
                                scope,
                                description
                            )
                        )
                        .build()
                );
            }

            return servers.build();
        }

        private void declareParameters(
            Scope scope,
            List<Parameter> parameters
        ) {
            for (Parameter parameter : parameters) {
                scope.declare(parameter.name(), parameter.line());
            }
        }

        private Json renderParameters(List<Parameter> parameters) {
            Json.ArrayBuilder rendered = Json.array();

            for (Parameter parameter : parameters) {
                rendered.add(
                    Json.object()
                        .put("name", Json.text(parameter.name()))
                        .put("type", Json.text(parameter.type()))
                        .put("line", renderLine(parameter.line()))
                        .build()
                );
            }

            return rendered.build();
        }

        /** Pass five: instances, in declaration order. */
        private Json renderInstances(MainDeclaration main) {
            Json.ArrayBuilder instances = Json.array();

            for (
                MainRebecDefinition definition :
                    main.getMainRebecDefinition()
            ) {
                instances.add(renderInstance(definition));
            }

            return instances.build();
        }

        private Json renderInstance(MainRebecDefinition definition) {
            String name = definition.getName();
            Integer line = definition.getLineNumber();

            ClassInfo info =
                classesByName.get(instanceClassNames.get(name));

            String priority =
                extractPriority(
                    definition.getAnnotations(),
                    "instance " + name
                );

            return Json.object()
                .put("name", Json.text(name))
                .put("className", Json.text(info.name()))
                .put("priority", renderPriority(priority))
                .put("line", renderLine(line))
                .put(
                    "bindings",
                    renderBindings(definition, info, name, line)
                )
                .put(
                    "arguments",
                    renderInstanceArguments(definition, info, name, line)
                )
                .build();
        }

        /**
         * R5. A positional list of bare instance names, one per known
         * rebec, each naming an instance whose class matches the
         * declared known-rebec type. Resolving bindings here is what
         * makes the topology static, and therefore what makes the
         * sender set of every message server computable.
         *
         * <p>The list is read through a wildcard so that this code does
         * not depend on the parser's element type for bindings; each
         * element is pattern-matched instead.
         */
        private Json renderBindings(
            MainRebecDefinition definition,
            ClassInfo info,
            String name,
            Integer line
        ) {
            List<?> bindings = definition.getBindings();
            int provided = bindings == null ? 0 : bindings.size();
            int expected = info.knownRebecs().size();

            if (provided != expected) {
                throw unsupported(
                    "instance " + name + " binding " + provided +
                    " known rebecs where class " + info.name() +
                    " declares " + expected + " (R5)" + at(line)
                );
            }

            Json.ArrayBuilder rendered = Json.array();

            for (int index = 0; index < provided; index++) {
                KnownRebec known = info.knownRebecs().get(index);

                String bound =
                    bindingName(
                        bindings.get(index),
                        name,
                        index,
                        line
                    );

                String boundClass = instanceClassNames.get(bound);

                if (boundClass == null) {
                    throw unsupported(
                        "instance " + name + " binding known rebec " +
                        known.name() + " to undeclared instance " +
                        bound + at(line)
                    );
                }

                if (!boundClass.equals(known.className())) {
                    throw unsupported(
                        "instance " + name + " binding known rebec " +
                        known.name() + " of type " +
                        known.className() + " to instance " + bound +
                        " of class " + boundClass + at(line)
                    );
                }

                rendered.add(
                    Json.object()
                        .put("knownRebec", Json.text(known.name()))
                        .put("instance", Json.text(bound))
                        .put("className", Json.text(boundClass))
                        .build()
                );
            }

            return rendered.build();
        }

        private String bindingName(
            Object candidate,
            String owner,
            int index,
            Integer line
        ) {
            if (
                candidate instanceof TermPrimary term &&
                term.getParentSuffixPrimary() == null &&
                term.getIndices().isEmpty()
            ) {
                return requireName(
                    term.getName(),
                    "known-rebec binding of instance " + owner
                );
            }

            throw unsupported(
                "a known-rebec binding of instance " + owner +
                " at position " + index +
                " that is not a bare instance name (R5)" + at(line)
            );
        }

        /**
         * R4 and D8. Fig. 4 writes {@code IntLit}, but our own type set
         * admits boolean, and a boolean-parameter constructor would
         * otherwise be uninstantiable, so a literal of the parameter's
         * declared type is required rather than an integer specifically.
         */
        private Json renderInstanceArguments(
            MainRebecDefinition definition,
            ClassInfo info,
            String name,
            Integer line
        ) {
            List<?> arguments = definition.getArguments();
            int provided = arguments == null ? 0 : arguments.size();
            List<Parameter> parameters = info.constructorParameters();

            if (provided != parameters.size()) {
                throw unsupported(
                    "instance " + name + " passing " + provided +
                    " constructor arguments where class " +
                    info.name() + " declares " + parameters.size() +
                    at(line)
                );
            }

            Json.ArrayBuilder rendered = Json.array();

            for (int index = 0; index < provided; index++) {
                rendered.add(
                    renderInstanceArgument(
                        arguments.get(index),
                        parameters.get(index),
                        name,
                        line
                    )
                );
            }

            return rendered.build();
        }

        private Json renderInstanceArgument(
            Object candidate,
            Parameter parameter,
            String owner,
            Integer line
        ) {
            String description =
                "constructor argument " + parameter.name() +
                " of instance " + owner;

            if (!(candidate instanceof Literal literal)) {
                throw unsupported(
                    "a non-literal " + description +
                    " (R4 admits a literal only)" + at(line)
                );
            }

            String text =
                requireNonNull(
                    literal.getLiteralValue(),
                    description + " has no literal value" + at(line)
                ).trim();

            if ("boolean".equals(parameter.type())) {
                if (!BOOLEAN_LITERALS.contains(text)) {
                    throw unsupported(
                        "a non-boolean " + description + " " + text +
                        at(line)
                    );
                }

                return Json.object()
                    .put("kind", Json.text("boolLiteral"))
                    .put("value", Json.bool("true".equals(text)))
                    .build();
            }

            if (BOOLEAN_LITERALS.contains(text)) {
                throw unsupported(
                    "a boolean " + description +
                    " where type " + parameter.type() +
                    " is declared" + at(line)
                );
            }

            return Json.object()
                .put("kind", Json.text("intLiteral"))
                .put(
                    "value",
                    Json.number(
                        integerLiteralText(text, description, line)
                    )
                )
                .build();
        }

        private static Json renderPriority(String priority) {
            return priority == null
                ? Json.nullValue()
                : Json.number(priority);
        }

        private static Json renderLine(Integer line) {
            return line == null
                ? Json.nullValue()
                : Json.number(line);
        }

        // ----------------------------------------------------------
        // SECTION: statements
        // ----------------------------------------------------------

        private Json renderBody(
            BlockStatement block,
            Scope scope,
            String description
        ) {
            if (block == null) {
                return Json.array().build();
            }

            return renderStatements(
                block.getStatements(),
                scope,
                description
            );
        }

        /**
         * R14. Four alternatives: assignment, send, {@code if},
         * {@code for}. Read through a wildcard and dispatched by
         * pattern so that one diagnostic covers every shape the parser
         * can hand back, including expressions used as statements.
         */
        private Json renderStatements(
            List<?> statements,
            Scope scope,
            String description
        ) {
            Json.ArrayBuilder rendered = Json.array();

            if (statements == null) {
                return rendered.build();
            }

            for (Object candidate : statements) {
                if (candidate instanceof BlockStatement nested) {
                    throw unsupported(
                        "a nested bare block in " + description +
                        " (R14)" + at(nested.getLineNumber())
                    );
                }

                rendered.add(
                    renderStatement(candidate, scope, description)
                );
            }

            return rendered.build();
        }

        private Json renderStatement(
            Object candidate,
            Scope scope,
            String description
        ) {
            if (candidate instanceof ConditionalStatement conditional) {
                return renderConditional(
                    conditional,
                    scope,
                    description
                );
            }

            if (candidate instanceof ForStatement loop) {
                return renderFor(loop, scope, description);
            }

            if (candidate instanceof DotPrimary dotPrimary) {
                return renderSend(dotPrimary, scope, description);
            }

            if (candidate instanceof BinaryExpression binary) {
                return renderAssignment(binary, scope, description);
            }

            if (candidate instanceof FieldDeclaration declaration) {
                throw unsupported(
                    "a local variable declaration in " + description +
                    " (R15: declare it in statevars, or use the " +
                    "initializer slot of a for header)" +
                    at(declaration.getLineNumber())
                );
            }

            if (candidate instanceof PlusSubExpression increment) {
                throw unsupported(
                    "the increment or decrement operator " +
                    increment.getOperator() + " in " + description +
                    " (R16 admits v = Expr only; write i = i + 1)" +
                    at(increment.getLineNumber())
                );
            }

            if (candidate instanceof CastExpression cast) {
                throw unsupported(
                    "a cast in " + description + " (D5)" +
                    at(cast.getLineNumber())
                );
            }

            if (candidate instanceof Statement statement) {
                throw unsupported(
                    "a statement of an unsupported shape in " +
                    description + " (R14 admits assignment, send, if " +
                    "and for)" + at(statement.getLineNumber())
                );
            }

            throw unsupported(
                "an unrecognized statement node in " + description
            );
        }

        /**
         * R16. The target is a bare name that must already denote a
         * state variable or a parameter-scoped local; compound
         * assignment is rejected because Fig. 4 writes {@code v = Expr}.
         */
        private Json renderAssignment(
            BinaryExpression binary,
            Scope scope,
            String description
        ) {
            Integer line = binary.getLineNumber();
            String operator = binary.getOperator();

            if (operator == null) {
                throw unsupported(
                    "an assignment with no operator in " + description +
                    at(line)
                );
            }

            if (!"=".equals(operator)) {
                if (isAssignmentOperator(operator)) {
                    throw unsupported(
                        "the compound assignment operator " + operator +
                        " in " + description +
                        " (R16 admits v = Expr only)" + at(line)
                    );
                }

                throw unsupported(
                    "a bare expression statement in " + description +
                    " (R14 has no Expr alternative, unlike Fig. 5's " +
                    "LFStmt)" + at(line)
                );
            }

            if (
                !(binary.getLeft() instanceof TermPrimary target) ||
                target.getParentSuffixPrimary() != null ||
                !target.getIndices().isEmpty()
            ) {
                throw unsupported(
                    "an assignment whose target is not a bare name " +
                    "in " + description + " (R16)" + at(line)
                );
            }

            String name =
                requireName(
                    target.getName(),
                    "assignment target in " + description
                );

            if (scope.owner.knownRebec(name) != null) {
                throw unsupported(
                    "an assignment to known rebec " + name + " in " +
                    description +
                    " (R21: the topology is fixed by main)" + at(line)
                );
            }

            if (!scope.isValue(name)) {
                throw unsupported(
                    "an assignment to undeclared name " + name +
                    " in " + description + at(line)
                );
            }

            return Json.object()
                .put("kind", Json.text("assign"))
                .put("target", Json.text(name))
                .put(
                    "value",
                    renderExpression(
                        binary.getRight(),
                        scope,
                        description
                    )
                )
                .put("line", renderLine(line))
                .build();
        }

        private static boolean isAssignmentOperator(String operator) {
            return operator.endsWith("=") &&
                !"==".equals(operator) &&
                !"!=".equals(operator) &&
                !"<=".equals(operator) &&
                !">=".equals(operator);
        }

        private Json renderConditional(
            ConditionalStatement conditional,
            Scope scope,
            String description
        ) {
            Integer line = conditional.getLineNumber();

            Json.ObjectBuilder rendered =
                Json.object()
                    .put("kind", Json.text("if"))
                    .put(
                        "condition",
                        renderExpression(
                            requireNonNull(
                                conditional.getCondition(),
                                "if without a condition in " +
                                description + at(line)
                            ),
                            scope,
                            description
                        )
                    )
                    .put(
                        "then",
                        renderBranch(
                            conditional.getStatement(),
                            scope,
                            description
                        )
                    );

            Statement otherwise = conditional.getElseStatement();

            rendered.put(
                "else",
                otherwise == null
                    ? Json.array().build()
                    : renderBranch(otherwise, scope, description)
            );

            return rendered.put("line", renderLine(line)).build();
        }

        /**
         * A branch is a statement list. Fig. 4 mandates braces, so a
         * braceless branch is strictly not derivable, but the parser
         * yields a single statement for one and normalizing it to a
         * one-element list changes no semantics.
         */
        private Json renderBranch(
            Statement branch,
            Scope scope,
            String description
        ) {
            if (branch == null) {
                return Json.array().build();
            }

            if (branch instanceof BlockStatement block) {
                return renderStatements(
                    block.getStatements(),
                    scope,
                    description
                );
            }

            return Json.array()
                .add(renderStatement(branch, scope, description))
                .build();
        }

        /**
         * D4 and D7. Fig. 4's header slots are all expressions, under
         * which no useful loop is derivable, so we follow Fig. 5's
         * {@code for(Stmt; Expr; Stmt)} shape. D7 additionally admits a
         * loop-local declaration in the initializer: forcing the counter
         * into statevars would enlarge the reachable state space the
         * model checker explores, so it is not semantics-preserving.
         */
        private Json renderFor(
            ForStatement loop,
            Scope scope,
            String description
        ) {
            Integer line = loop.getLineNumber();
            ForInitializer initializer = loop.getForInitializer();

            if (initializer == null) {
                throw unsupported(
                    "a for loop with no initializer in " + description +
                    at(line)
                );
            }

            List<String> declared = new ArrayList<>();

            Json init =
                renderForInitializer(
                    initializer,
                    scope,
                    description,
                    declared,
                    line
                );

            Json condition =
                renderExpression(
                    requireNonNull(
                        loop.getCondition(),
                        "a for loop with no condition in " +
                        description + at(line)
                    ),
                    scope,
                    description
                );

            Json update =
                renderStatement(
                    singleNode(
                        loop.getForIncrement(),
                        "for update",
                        description,
                        line
                    ),
                    scope,
                    description
                );

            Json body =
                renderBranch(
                    loop.getStatement(),
                    scope,
                    description
                );

            for (String name : declared) {
                scope.undeclare(name);
            }

            return Json.object()
                .put("kind", Json.text("for"))
                .put("init", init)
                .put("condition", condition)
                .put("update", update)
                .put("body", body)
                .put("line", renderLine(line))
                .build();
        }

        private Json renderForInitializer(
            ForInitializer initializer,
            Scope scope,
            String description,
            List<String> declared,
            Integer line
        ) {
            FieldDeclaration declaration =
                initializer.getFieldDeclaration();

            if (declaration != null) {
                String type =
                    typeName(
                        declaration.getType(),
                        "for-loop counter in " + description,
                        line
                    );

                if (!VALUE_TYPES.contains(type)) {
                    throw unsupported(
                        "a for-loop counter of type " + type +
                        " in " + description + at(line)
                    );
                }

                VariableDeclarator declarator =
                    requireOne(
                        declaration.getVariableDeclarators(),
                        "for-loop counter in " + description
                    );

                String name =
                    requireName(
                        declarator.getVariableName(),
                        "for-loop counter in " + description
                    );

                VariableInitializer value =
                    declarator.getVariableInitializer();

                if (
                    !(value instanceof OrdinaryVariableInitializer
                        ordinary)
                ) {
                    throw unsupported(
                        "a for-loop counter " + name +
                        " without a simple initial value in " +
                        description + at(line)
                    );
                }

                scope.declare(name, line);
                declared.add(name);

                return Json.object()
                    .put("kind", Json.text("declare"))
                    .put("name", Json.text(name))
                    .put("type", Json.text(type))
                    .put(
                        "value",
                        renderExpression(
                            ordinary.getValue(),
                            scope,
                            description
                        )
                    )
                    .put("line", renderLine(line))
                    .build();
            }

            return renderStatement(
                singleNode(
                    initializer.getExpressions(),
                    "for initializer",
                    description,
                    line
                ),
                scope,
                description
            );
        }

        /**
         * Accepts either a single node or a one-element list, so this
         * code is independent of whether the parser models a for-header
         * slot as one expression or as a list of them.
         */
        private Object singleNode(
            Object candidate,
            String slot,
            String description,
            Integer line
        ) {
            if (candidate instanceof List<?> nodes) {
                if (nodes.size() != 1) {
                    throw unsupported(
                        "a " + slot + " with " + nodes.size() +
                        " entries in " + description +
                        " (exactly one is admitted)" + at(line)
                    );
                }

                return nodes.get(0);
            }

            if (candidate == null) {
                throw unsupported(
                    "an empty " + slot + " in " + description +
                    " (Fig. 4 marks the slot optional, but a loop " +
                    "without one does not terminate observably)" +
                    at(line)
                );
            }

            return candidate;
        }

        /**
         * R18, R19, R20, D6 and D9. The receiver is {@code self} or a
         * declared known rebec, the message server must exist on the
         * resolved target class with matching arity, {@code deadline}
         * is rejected, and {@code after} is optional but must be a
         * non-negative integer literal when present.
         */
        private Json renderSend(
            DotPrimary dotPrimary,
            Scope scope,
            String description
        ) {
            Integer line = dotPrimary.getLineNumber();
            Object left = dotPrimary.getLeft();

            if (left instanceof CastExpression) {
                throw unsupported(
                    "A3: a send whose receiver is a cast in " +
                    description +
                    ", which makes the target statically unresolvable" +
                    at(line)
                );
            }

            if (
                !(left instanceof TermPrimary receiver) ||
                receiver.getParentSuffixPrimary() != null ||
                !receiver.getIndices().isEmpty()
            ) {
                throw unsupported(
                    "a send whose receiver is not a bare name in " +
                    description + " (R18)" + at(line)
                );
            }

            String receiverName =
                requireName(
                    receiver.getName(),
                    "send receiver in " + description
                );

            if (SENDER_REFERENCE.equals(receiverName)) {
                throw unsupported(
                    "A4: a send to the implicit sender in " +
                    description +
                    ", whose value is not statically known" + at(line)
                );
            }

            ClassInfo targetClass;
            Json target;

            if (SELF_REFERENCE.equals(receiverName)) {
                targetClass = scope.owner;

                target = Json.object()
                    .put("kind", Json.text("self"))
                    .build();
            } else {
                KnownRebec known = scope.owner.knownRebec(receiverName);

                if (known == null) {
                    throw unsupported(
                        "D6: a send to " + receiverName + " in " +
                        description +
                        ", which is not self and not a known rebec of " +
                        scope.owner.name() + at(line)
                    );
                }

                targetClass = classesByName.get(known.className());

                target = Json.object()
                    .put("kind", Json.text("knownRebec"))
                    .put("name", Json.text(known.name()))
                    .build();
            }

            if (
                !(dotPrimary.getRight() instanceof TermPrimary method)
            ) {
                throw unsupported(
                    "a send with no message-server name in " +
                    description + at(line)
                );
            }

            if (!method.getIndices().isEmpty()) {
                throw unsupported(
                    "an indexed message-server call in " + description +
                    at(line)
                );
            }

            String messageServerName =
                requireName(
                    method.getName(),
                    "message server in " + description
                );

            MsgsrvDeclaration server =
                targetClass.messageServer(messageServerName);

            if (server == null) {
                throw unsupported(
                    "a send of " + messageServerName +
                    ", which class " + targetClass.name() +
                    " does not declare, in " + description + at(line)
                );
            }

            ParentSuffixPrimary suffix =
                method.getParentSuffixPrimary();

            if (suffix == null) {
                throw unsupported(
                    "a send with no argument list in " + description +
                    at(line)
                );
            }

            Expression after = null;

            if (
                suffix instanceof TimedRebecaParentSuffixPrimary timed
            ) {
                if (timed.getDeadlineExpression() != null) {
                    throw unsupported(
                        "deadline(...) in " + description +
                        " (R20: after is the only timing primitive)" +
                        at(line)
                    );
                }

                after = timed.getAfterExpression();
            }

            List<Parameter> parameters =
                readParameters(
                    server.getFormalParameters(),
                    "message server " + targetClass.name() + "." +
                    messageServerName
                );

            return Json.object()
                .put("kind", Json.text("send"))
                .put("target", target)
                .put("targetClassName", Json.text(targetClass.name()))
                .put("messageServer", Json.text(messageServerName))
                .put(
                    "arguments",
                    renderSendArguments(
                        suffix.getArguments(),
                        parameters,
                        messageServerName,
                        scope,
                        description,
                        line
                    )
                )
                .put("after", renderAfter(after, description))
                .put("line", renderLine(line))
                .build();
        }

        private Json renderSendArguments(
            List<?> arguments,
            List<Parameter> parameters,
            String messageServerName,
            Scope scope,
            String description,
            Integer line
        ) {
            int provided = arguments == null ? 0 : arguments.size();

            if (provided != parameters.size()) {
                throw unsupported(
                    "a send of " + messageServerName + " with " +
                    provided + " arguments where " + parameters.size() +
                    " are declared, in " + description + at(line)
                );
            }

            Json.ArrayBuilder rendered = Json.array();

            for (int index = 0; index < provided; index++) {
                rendered.add(
                    renderExpression(
                        arguments.get(index),
                        scope,
                        description
                    )
                );
            }

            return rendered.build();
        }

        /**
         * D9. Fig. 4 writes {@code after(Expr)}, but an external send
         * becomes a Lingua Franca connection whose {@code after} delay
         * must be static, so a runtime-valued delay is not translatable
         * and a literal is required. Absence is emitted as null rather
         * than as zero: R19's default belongs to the translation, and
         * this document is an abstract syntax tree.
         */
        private Json renderAfter(
            Expression after,
            String description
        ) {
            if (after == null) {
                return Json.nullValue();
            }

            Integer line = after.getLineNumber();

            if (!(after instanceof Literal literal)) {
                throw unsupported(
                    "a non-literal after delay in " + description +
                    " (D9: a Lingua Franca connection delay is static)" +
                    at(line)
                );
            }

            return Json.object()
                .put("kind", Json.text("intLiteral"))
                .put(
                    "value",
                    Json.number(
                        integerLiteralText(
                            literal.getLiteralValue(),
                            "after delay in " + description,
                            line
                        )
                    )
                )
                .build();
        }

        // ----------------------------------------------------------
        // SECTION: expressions
        // ----------------------------------------------------------

        /**
         * D5. The paper defines no expression language at all: Fig. 4
         * uses {@code Expr} seven times and never produces it, and the
         * only handles in the prose are semantic
         * ({@code eval(expr, e)}). So this set is the tool's choice and
         * must never be presented as a paper citation.
         */
        private Json renderExpression(
            Object candidate,
            Scope scope,
            String description
        ) {
            if (candidate == null) {
                throw unsupported(
                    "a missing expression in " + description
                );
            }

            if (candidate instanceof Literal literal) {
                return renderLiteral(literal, description);
            }

            if (candidate instanceof TermPrimary term) {
                return renderTerm(term, scope, description);
            }

            if (candidate instanceof BinaryExpression binary) {
                return renderBinary(binary, scope, description);
            }

            if (candidate instanceof UnaryExpression unary) {
                return renderUnary(unary, scope, description);
            }

            if (candidate instanceof PlusSubExpression increment) {
                throw unsupported(
                    "the increment or decrement operator " +
                    increment.getOperator() + " in " + description +
                    " (write i = i + 1)" +
                    at(increment.getLineNumber())
                );
            }

            if (candidate instanceof TernaryExpression ternary) {
                throw unsupported(
                    "a ternary conditional in " + description +
                    " (D5; use an if statement)" +
                    at(ternary.getLineNumber())
                );
            }

            if (candidate instanceof CastExpression cast) {
                throw unsupported(
                    "a cast in " + description + " (D5)" +
                    at(cast.getLineNumber())
                );
            }

            if (candidate instanceof NonDetExpression nonDet) {
                throw unsupported(
                    "a nondeterministic choice ?(...) in " +
                    description +
                    " (R20: the fragment has no nondeterministic " +
                    "expression, and an unresolved observable choice " +
                    "is outside the supported fragment per III-G)" +
                    at(nonDet.getLineNumber())
                );
            }

            if (candidate instanceof DotPrimary dotPrimary) {
                throw unsupported(
                    "a message send in expression position in " +
                    description +
                    " (a send is a statement and yields no value)" +
                    at(dotPrimary.getLineNumber())
                );
            }

            if (candidate instanceof Expression expression) {
                throw unsupported(
                    "an expression of an unsupported shape in " +
                    description + " (D5)" +
                    at(expression.getLineNumber())
                );
            }

            throw unsupported(
                "an unrecognized expression node in " + description
            );
        }

        /**
         * {@link Literal} carries only its source text, with no type
         * field, so the kind has to be decided from the text itself.
         */
        private Json renderLiteral(
            Literal literal,
            String description
        ) {
            Integer line = literal.getLineNumber();

            String text =
                requireNonNull(
                    literal.getLiteralValue(),
                    "a literal with no value in " + description +
                    at(line)
                ).trim();

            if (BOOLEAN_LITERALS.contains(text)) {
                return Json.object()
                    .put("kind", Json.text("boolLiteral"))
                    .put("value", Json.bool("true".equals(text)))
                    .put("line", renderLine(line))
                    .build();
            }

            return Json.object()
                .put("kind", Json.text("intLiteral"))
                .put(
                    "value",
                    Json.number(
                        integerLiteralText(
                            text,
                            "literal in " + description,
                            line
                        )
                    )
                )
                .put("line", renderLine(line))
                .build();
        }

        private Json renderTerm(
            TermPrimary term,
            Scope scope,
            String description
        ) {
            Integer line = term.getLineNumber();

            String name =
                requireName(
                    term.getName(),
                    "a name in " + description
                );

            if (term.getParentSuffixPrimary() != null) {
                throw unsupported(
                    "a call to " + name + " in " + description +
                    " (D5 admits no function calls)" + at(line)
                );
            }

            if (!term.getIndices().isEmpty()) {
                throw unsupported(
                    "an indexed access to " + name + " in " +
                    description +
                    " (R16: the fragment has no arrays)" + at(line)
                );
            }

            if (CLOCK_REFERENCE.equals(name)) {
                throw unsupported(
                    "a read of the logical clock now in " +
                    description +
                    ", which the fragment does not expose as a value" +
                    at(line)
                );
            }

            if (SENDER_REFERENCE.equals(name)) {
                throw unsupported(
                    "A4: a read of the implicit sender in " +
                    description +
                    ", whose value is not statically known" + at(line)
                );
            }

            if (SELF_REFERENCE.equals(name)) {
                throw unsupported(
                    "a use of self as a value in " + description +
                    " (self is a send receiver only, R18)" + at(line)
                );
            }

            if (scope.owner.knownRebec(name) != null) {
                throw unsupported(
                    "a use of known rebec " + name +
                    " as a value in " + description +
                    " (a rebec reference is not a value, A1)" + at(line)
                );
            }

            if (!scope.isValue(name)) {
                throw unsupported(
                    "a read of undeclared name " + name + " in " +
                    description + at(line)
                );
            }

            return Json.object()
                .put("kind", Json.text("variable"))
                .put("name", Json.text(name))
                .put("line", renderLine(line))
                .build();
        }

        private Json renderBinary(
            BinaryExpression binary,
            Scope scope,
            String description
        ) {
            Integer line = binary.getLineNumber();

            String operator =
                requireNonNull(
                    binary.getOperator(),
                    "a binary expression with no operator in " +
                    description + at(line)
                );

            if (isAssignmentOperator(operator)) {
                throw unsupported(
                    "an assignment in expression position in " +
                    description + " (R16)" + at(line)
                );
            }

            if (!BINARY_OPERATORS.contains(operator)) {
                throw unsupported(
                    "the binary operator " + operator + " in " +
                    description + " (D5 admits " +
                    String.join(" ", BINARY_OPERATORS) + ")" + at(line)
                );
            }

            return Json.object()
                .put("kind", Json.text("binary"))
                .put("operator", Json.text(operator))
                .put(
                    "left",
                    renderExpression(
                        binary.getLeft(),
                        scope,
                        description
                    )
                )
                .put(
                    "right",
                    renderExpression(
                        binary.getRight(),
                        scope,
                        description
                    )
                )
                .put("line", renderLine(line))
                .build();
        }

        private Json renderUnary(
            UnaryExpression unary,
            Scope scope,
            String description
        ) {
            Integer line = unary.getLineNumber();

            String operator =
                requireNonNull(
                    unary.getOperator(),
                    "a unary expression with no operator in " +
                    description + at(line)
                );

            if (!UNARY_OPERATORS.contains(operator)) {
                throw unsupported(
                    "the unary operator " + operator + " in " +
                    description + " (D5 admits " +
                    String.join(" ", UNARY_OPERATORS) + ")" + at(line)
                );
            }

            return Json.object()
                .put("kind", Json.text("unary"))
                .put("operator", Json.text(operator))
                .put(
                    "operand",
                    renderExpression(
                        unary.getExpression(),
                        scope,
                        description
                    )
                )
                .put("line", renderLine(line))
                .build();
        }
    }

    // --------------------------------------------------------------
    // SECTION: json value model
    // --------------------------------------------------------------

    /**
     * A minimal immutable JSON value tree with one recursive renderer.
     *
     * <p>The earlier exporters concatenated their output by hand. That
     * is tolerable for a flat record and unmanageable for statement and
     * expression trees of arbitrary depth, where a single misplaced
     * comma or indent is both easy to write and hard to see. Building a
     * value and rendering it once removes that whole class of bug.
     *
     * <p>Member order is insertion order and array order is source
     * order. Neither survives to the published fixture, because the
     * staging harness re-serializes every published JSON document with
     * sorted keys, but both make the raw exporter output readable when
     * a fixture disagrees and someone has to diff it by eye.
     */
    private static final class Json {

        private enum Kind {
            LITERAL,
            TEXT,
            ARRAY,
            OBJECT
        }

        private final Kind kind;

        private final String payload;

        private final List<Json> elements;

        private final List<String> keys;

        private final List<Json> values;

        private Json(
            Kind kind,
            String payload,
            List<Json> elements,
            List<String> keys,
            List<Json> values
        ) {
            this.kind = kind;
            this.payload = payload;
            this.elements = elements;
            this.keys = keys;
            this.values = values;
        }

        private static Json text(String value) {
            return new Json(
                Kind.TEXT,
                requireNonNull(value, "json string is null"),
                null,
                null,
                null
            );
        }

        private static Json number(int value) {
            return new Json(
                Kind.LITERAL,
                Integer.toString(value),
                null,
                null,
                null
            );
        }

        /**
         * Emits an already-validated numeric literal without reparsing
         * it, so the exact digits the model author wrote survive into
         * the JSON.
         */
        private static Json number(String literal) {
            return new Json(
                Kind.LITERAL,
                requireNonNull(literal, "json number is null"),
                null,
                null,
                null
            );
        }

        private static Json bool(boolean value) {
            return new Json(
                Kind.LITERAL,
                Boolean.toString(value),
                null,
                null,
                null
            );
        }

        private static Json nullValue() {
            return new Json(Kind.LITERAL, "null", null, null, null);
        }

        private static ArrayBuilder array() {
            return new ArrayBuilder();
        }

        private static ObjectBuilder object() {
            return new ObjectBuilder();
        }

        private String render(int indent) {
            switch (kind) {
                case LITERAL:
                    return payload;

                case TEXT:
                    return jsonString(payload);

                case ARRAY:
                    return renderSequence(indent);

                case OBJECT:
                    return renderMembers(indent);

                default:
                    throw new IllegalStateException(
                        "unreachable json kind " + kind
                    );
            }
        }

        private String renderSequence(int indent) {
            if (elements.isEmpty()) {
                return "[]";
            }

            StringBuilder builder = new StringBuilder("[\n");

            for (int index = 0; index < elements.size(); index++) {
                builder.append(spaces(indent + 1));

                builder.append(
                    elements.get(index).render(indent + 1)
                );

                if (index + 1 < elements.size()) {
                    builder.append(',');
                }

                builder.append('\n');
            }

            return builder
                .append(spaces(indent))
                .append(']')
                .toString();
        }

        private String renderMembers(int indent) {
            if (keys.isEmpty()) {
                return "{}";
            }

            StringBuilder builder = new StringBuilder("{\n");

            for (int index = 0; index < keys.size(); index++) {
                builder.append(spaces(indent + 1));
                builder.append(jsonString(keys.get(index)));
                builder.append(": ");

                builder.append(
                    values.get(index).render(indent + 1)
                );

                if (index + 1 < keys.size()) {
                    builder.append(',');
                }

                builder.append('\n');
            }

            return builder
                .append(spaces(indent))
                .append('}')
                .toString();
        }

        private static final class ArrayBuilder {

            private final List<Json> elements = new ArrayList<>();

            private ArrayBuilder add(Json element) {
                elements.add(
                    requireNonNull(element, "json array element is null")
                );

                return this;
            }

            private Json build() {
                return new Json(
                    Kind.ARRAY,
                    null,
                    List.copyOf(elements),
                    null,
                    null
                );
            }
        }

        private static final class ObjectBuilder {

            private final List<String> keys = new ArrayList<>();

            private final List<Json> values = new ArrayList<>();

            private ObjectBuilder put(String key, Json value) {
                keys.add(requireNonNull(key, "json member key is null"));

                values.add(
                    requireNonNull(value, "json member value is null")
                );

                return this;
            }

            private Json build() {
                return new Json(
                    Kind.OBJECT,
                    null,
                    null,
                    List.copyOf(keys),
                    List.copyOf(values)
                );
            }
        }
    }

    // --------------------------------------------------------------
    // Diagnostics
    // --------------------------------------------------------------

    /**
     * The single rejection sink. Every unsupported construct funnels
     * through here so that the diagnostic corpus is greppable and so
     * that the runner's exit path is uniform: there is no catch and no
     * explicit exit code, the exception propagates out of
     * {@code main}, the exec plugin wraps it, Maven exits non-zero,
     * and the calling shell script aborts under {@code set -e}.
     */
    private static IllegalArgumentException unsupported(
        String construct
    ) {
        return new IllegalArgumentException(
            "unsupported by the ReLico general parser bridge: " +
            construct
        );
    }

    /**
     * Every diagnostic carries a source line where the AST offers one.
     * The parser leaves {@code lineNumber} null on synthesized nodes,
     * so this degrades to the empty string rather than printing null.
     */
    private static String at(Integer line) {
        return line == null ? "" : " (line " + line + ")";
    }

    private static <T> T requireOne(
        List<T> values,
        String description
    ) {
        if (values == null || values.size() != 1) {
            int size = values == null ? 0 : values.size();

            throw new IllegalArgumentException(
                "expected exactly one " + description +
                ", received " + size
            );
        }

        return values.get(0);
    }

    private static void requireEmpty(
        Collection<?> values,
        String description
    ) {
        if (values != null && !values.isEmpty()) {
            throw unsupported(description);
        }
    }

    private static void requireEmpty(
        Object value,
        String description
    ) {
        if (value != null) {
            throw unsupported(description);
        }
    }

    private static void requireUnique(
        Set<String> seen,
        String name,
        String description
    ) {
        if (!seen.add(name)) {
            throw unsupported("duplicate " + description + " " + name);
        }
    }

    private static <T> T requireNonNull(T value, String description) {
        if (value == null) {
            throw new IllegalArgumentException(description);
        }

        return value;
    }

    private static String requireName(String name, String description) {
        if (name == null || name.isBlank()) {
            throw new IllegalArgumentException(
                description + " has no name"
            );
        }

        return name;
    }

    private static String spaces(int count) {
        return "  ".repeat(count);
    }

    private static String jsonString(String value) {
        StringBuilder builder = new StringBuilder("\"");

        for (int index = 0; index < value.length(); index++) {
            char character = value.charAt(index);

            switch (character) {
                case '"' -> builder.append("\\\"");
                case '\\' -> builder.append("\\\\");
                case '\b' -> builder.append("\\b");
                case '\f' -> builder.append("\\f");
                case '\n' -> builder.append("\\n");
                case '\r' -> builder.append("\\r");
                case '\t' -> builder.append("\\t");
                default -> {
                    if (character < 0x20) {
                        builder.append(
                            String.format("\\u%04x", (int) character)
                        );
                    } else {
                        builder.append(character);
                    }
                }
            }
        }

        return builder.append('"').toString();
    }
}
