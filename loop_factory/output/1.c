/*@
  requires 1;
*/
int main1(int a,int k,int m){
  int x, y, c;

  x=1;
  y=a;
  c=1;

  
  /*@

    loop invariant y == (a - 1) * x + 1;

    loop invariant c >= 1;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop assigns c, x, y;

  */
  while (c<m) {
      c = c+1;
      x = x*a+1;
      y = y*a;
  }

  /*@ assert 1; */
}