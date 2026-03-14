int main1(int t,int j){
  int fl, m7j, wt, o, pg5s, f;
  fl=j-9;
  m7j=0;
  wt=0;
  o=0;
  pg5s=0;
  f=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= pg5s <= 4;
  loop invariant -4*m7j <= wt <= 4*m7j;
  loop invariant fl == j - 9;
  loop invariant 0 <= o <= 4;
  loop invariant fl == \at(j, Pre) - 9;
  loop invariant (7 <= f);
  loop invariant (f <= 7 + 4*m7j);
  loop invariant (m7j >= 0);
  loop assigns o, m7j, wt, f, pg5s;
*/
while (m7j<fl) {
      o = m7j%5;
      if (!(!(m7j>=f))) {
          pg5s = (m7j-f)%5;
          wt = wt+o-pg5s;
      }
      else {
          wt = wt + o;
      }
      m7j = m7j + 1;
      f = f + pg5s;
  }
}