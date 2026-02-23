int main1(int n,int q){
  int r, c, w;

  r=32;
  c=0;
  w=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == 32;
  loop invariant 0 <= c;
  loop invariant c <= r;
  loop invariant c == 0 ==> w == 0;
  loop invariant c >= 0;
  loop assigns c, w;
*/
while (c<=r-1) {
      w = w-w;
      w = w+4;
      c = c+1;
  }

}
