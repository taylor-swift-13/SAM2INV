int main3(int a,int b,int n){
  int x, y, c;

  x=1;
  y=b;
  c=1;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant c >= 1;

    loop invariant y == (b - 1) * x + 1;

    loop assigns c, x, y;

  */
  while (c<a) {
      c = c+1;
      x = x*b+1;
      y = y*b;
  }

  /*@ assert 1; */
}