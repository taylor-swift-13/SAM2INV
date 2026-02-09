void foo(){
    int x = 1;
    int y = 0;
    int z = 0;
    
    while (y < 100000) {
        x = x + y;
        y = y + 1;
    }

    while (z < 100000) {
    
        z = z + 1;
    }

    /*@ assert x >= y; */
}