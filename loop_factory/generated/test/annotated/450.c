int main1(int q){
  int o3, pat, otn, go, c3;
  o3=77;
  pat=o3;
  otn=0;
  go=0;
  c3=pat;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant otn == go * q;
  loop invariant go <= o3;
  loop invariant 0 <= go;
  loop assigns go, otn;
*/
while (1) {
      if (!(go<o3)) {
          break;
      }
      go++;
      otn = otn + q;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant go - q*(o3 - c3) == 77;
  loop invariant 0 <= c3 - o3;
  loop invariant go - q * o3 == 77 * (1 - q);
  loop invariant 0 <= o3;
  loop assigns go, o3;
*/
while (o3<c3) {
      go = go + q;
      o3 = o3 + 1;
  }
}