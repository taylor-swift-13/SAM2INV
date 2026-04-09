int main1(int a){
  int sb, m, c, t3xt, hrq;
  sb=a;
  m=0;
  c=-2;
  t3xt=20;
  hrq=sb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (c == -2 + 3*(a - sb));
  loop invariant (t3xt == 20);
  loop invariant m == 0;
  loop invariant c == -2 + 3 * (\at(a, Pre) - sb);
  loop invariant (\at(a, Pre) - sb) >= 0;
  loop invariant 2 * (hrq - \at(a, Pre)) == (\at(a, Pre) - sb) * (3 * (\at(a, Pre) - sb) - 1);
  loop invariant hrq == \at(a, Pre) + (-2) * (\at(a, Pre) - sb)
                         + 3 * ((\at(a, Pre) - sb) * ((\at(a, Pre) - sb) + 1)) / 2;
  loop invariant hrq == \at(a, Pre) - 2 * (\at(a, Pre) - sb)
                      + 3 * ((\at(a, Pre) - sb) * ((\at(a, Pre) - sb) + 1)) / 2;
  loop assigns c, sb, t3xt, hrq;
*/
while (1) {
      if (!(m < sb)) {
          break;
      }
      c = c + 3;
      sb--;
      t3xt = t3xt+t3xt-t3xt;
      hrq = hrq + c;
  }
}