int main1(){
  int sxu, xj, fe, jq, i, vk4;
  sxu=105;
  xj=0;
  fe=31;
  jq=0;
  i=1;
  vk4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fe + jq == 31;
  loop invariant 0 <= fe;
  loop invariant fe <= 31;
  loop invariant jq <= (i - 1) * i / 2;
  loop invariant i == xj + 1;
  loop invariant 0 <= xj <= sxu;
  loop assigns vk4, xj, jq, i, fe;
*/
while (1) {
      if (!(fe>0&&xj<sxu)) {
          break;
      }
      if (fe<=i) {
          vk4 = fe;
      }
      else {
          vk4 = i;
      }
      xj++;
      jq = jq + vk4;
      i = i + 1;
      fe = fe - vk4;
  }
}