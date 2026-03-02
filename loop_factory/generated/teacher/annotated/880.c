int main1(int n,int q){
  int h, d, w;

  h=26;
  d=0;
  w=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (n == \at(n, Pre)) && (q == \at(q, Pre)) && ((w == -3) || (w >= 0));
  loop invariant w >= -3;
  loop invariant h == 26;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant w == -3 || w >= 0;
  loop invariant n == \at(n, Pre) && q == \at(q, Pre);
  loop assigns w;
*/
while (1) {
      w = w+3;
      w = w*w;
  }

}
