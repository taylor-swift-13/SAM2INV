int main1(int g,int v){
  int alxm, a, l, q;
  alxm=9;
  a=alxm;
  l=a;
  q=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l + a == 18;
  loop invariant q - 4 * (9 - a) == \at(g, Pre);
  loop invariant q + 4 * a == \at(g, Pre) + 4 * alxm;
  loop invariant q == g + 4 * (alxm - a);
  loop invariant 0 <= a <= 9;
  loop assigns a, l, q;
*/
for (; a>=1; a -= 1) {
      l = l + 1;
      q = q - 1;
      q = q + 5;
  }
}