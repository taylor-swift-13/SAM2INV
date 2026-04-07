int main1(int f){
  int xx, l2, lf, l;
  xx=f-5;
  l2=0;
  lf=f;
  l=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= l2;
  loop invariant l == l2 * l2;
  loop invariant lf == f + l2 + (l2*(l2+1)*(2*l2+1))/6;
  loop invariant xx == \at(f, Pre) - 5;
  loop invariant (0 <= l2 && (xx < 0 || l2 <= xx));
  loop invariant (xx == f - 5);
  loop assigns l, lf, l2;
*/
while (1) {
      if (!(l2 < xx)) {
          break;
      }
      l = l + 2*l2 + 1;
      lf += l;
      l2 += 1;
      lf = lf + 1;
  }
}