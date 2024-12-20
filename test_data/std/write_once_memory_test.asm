use std::machines::write_once_memory::WriteOnceMemory;

let main_degree: int = 256;
let memory_degree: int = 256;

machine Main with degree: main_degree {
    WriteOnceMemory memory(memory_degree, memory_degree);

    reg pc[@pc];
    reg X[<=];
    reg Y[<=];
    reg A;

    instr mload X -> Y link => memory.access(X, Y);
    instr mstore X, Y -> link => memory.access(X, Y);

    instr assert_eq X, Y { X = Y }

    function main {
        // Minimal address: 0
        mstore 0, 1234;
        A <== mload(0);
        assert_eq A, 1234;

        // Maximal address: N - 1
        mstore 255, 1234;
        A <== mload(255);
        assert_eq A, 1234;

        // Maximal value: Any field element
        mstore 17, -1;
        A <== mload(17);
        assert_eq A, -1;

        // Read same value again
        A <== mload(17);
        assert_eq A, -1;

        return;
    }
}
