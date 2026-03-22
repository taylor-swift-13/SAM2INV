int main1(int f,int u){
  int i, d1, m7, ywh, h;
  i=u-5;
  d1=0;
  m7=0;
  ywh=0;
  h=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ywh == m7*(m7 - 1) / 2;
  loop invariant 0 <= m7;
  loop invariant i == u - 5;
  loop assigns f, m7, ywh;
*/
while (1) {
      if (!(m7<i)) {
          break;
      }
      ywh += m7;
      m7 += 1;
      f += ywh;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= d1 <= m7;
  loop invariant u - \at(u, Pre) == m7*d1 - d1*(d1-1)/2;
  loop assigns u, d1, h;
*/
while (1) {
      if (!(d1<m7)) {
          break;
      }
      h = m7-d1;
      u += h;
      d1 += 1;
  }
}