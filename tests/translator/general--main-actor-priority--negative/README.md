# General main-actor-priority rejection test

This externally provisioned translator test pins the historical single-main-actor payload frontend
boundary. The annotated main actor must be rejected, while otherwise identical input without the
annotation and input carrying local message-server priority must be accepted.

The case is discovered by `tools/relico_test.sh` when `RELICO_PARSER_ARTIFACT` names the required
parser archive. Its runner asserts the expected diagnostic and verifies that rejection produces no
JSON, decoded AST, translated LF, or runtime artifact.
