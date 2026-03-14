int main1(){
  int iw, o, j, ted, pyz, ze3a;
  iw=1+19;
  o=0;
  j=0;
  ted=0;
  pyz=0;
  ze3a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ze3a + pyz + ted <= o;
  loop invariant 0 <= ze3a;
  loop invariant 0 <= pyz;
  loop invariant 0 <= ted;
  loop invariant j <= 2 * o;
  loop invariant 0 <= o <= iw;
  loop invariant j >= o;
  loop assigns o, j, pyz, ted, ze3a;
*/
while (o<iw) {
      if (!(!(o%11==0))) {
          if (o%8==0) {
              pyz++;
          }
          else {
              if (o%7==0) {
                  ted += 1;
              }
              else {
                  j++;
              }
          }
      }
      else {
          ze3a += 1;
      }
      o = o + 1;
      j++;
  }
}