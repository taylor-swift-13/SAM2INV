int main1(int n,int q){
  int r, c, w;

  r=32;
  c=0;
  w=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c && c <= r;
  loop invariant (c==0 && w==3) || (c>=1 && w==4);
  loop invariant 3 <= w && w <= 4;
  loop invariant n == \at(n, Pre) && q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == 32;
  loop invariant w == 3 || w == 4;
  loop invariant 0 <= w && w <= 4*c + 3;
  loop invariant c <= r;
  loop invariant (c == 0) ==> (w == 3);
  loop invariant (c == 0 ==> w == 3) && (c >= 1 ==> w == 4);
  loop assigns c, w;
*/
while (c<r) {
      if (w+7<r) {
          w = w-w;
      }
      w = w+4;
      c = c+1;
  }

}
