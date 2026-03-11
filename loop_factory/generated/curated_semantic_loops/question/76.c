int main1(int k,int p){
  int g, l, m, v;

  g=54;
  l=g;
  m=l;
  v=g;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (m<g) {
      if (m<g) {
          m = m+1;
      }
      m = m+1;
  }
/*@
  assert !(m<g) &&
         (m <= g + 1);
*/

}
