int main1(int m,int p){
  int f, j, o, i, x;

  f=49;
  j=f;
  o=1;
  i=p;
  x=f;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x + j == 2*f;
  loop invariant 0 <= j;
  loop invariant j <= f;
  loop invariant p == \at(p, Pre);
  loop invariant o == 1 + 3*(f - j);
  loop invariant x == 2*f - j;
  loop invariant m == \at(m, Pre);
  loop invariant f == 49;
  loop assigns o, x, j;
*/
while (j>0) {
      o = o+3;
      x = x+1;
      j = j-1;
  }

}
