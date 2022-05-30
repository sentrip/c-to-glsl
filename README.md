# C-to-GLSL

## Why

This library was created to facilitate writing compute shaders in GLSL. 


## Concepts

### Global Arrays
Global Arrays are the solution to using C-like pointers in GLSL. 
To define a Global Array:

```c
#ifdef GLSL
static int* my_global = (binding=0, set=0, count=1);
#endif
```

Which is removed by the preprocessor in C, and translates to the following in GLSL:
```glsl
layout(std430, binding = 0, set = 0) buffer my_global_t { int data[]; } my_global_arr[1];
```

To use a Global Array:
```c
// NOTE: the name of the argument to the function must be the same as the global array
int  read_my_global(const int* my_global)       { return my_global[0]; }
void modify_my_global(int* my_global, int v)    { my_global[0] = v; }
```

Which remains the same in c, and translates to the following in GLSL:
```glsl
int  read_my_global(uint my_global)             { return my_global_arr[my_global].data[0]; }
void modify_my_global(uint my_global, int v)    { my_global_arr[my_global].data[0] = v; }
```

To use functions that use Global Arrays in C:
```c
int main() {
    int data[8];
    const int x = read_my_global(data);
    write_my_global(data, 999u);
    return 0;
}
```

To use functions that use Global Arrays in GLSL:
```glsl
void main() {
    const int x = read_my_global(0u);
    write_my_global(0u, 999u);
}
```
