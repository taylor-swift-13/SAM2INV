int main1(int k){
  int uy, y, jfe, ut, ye, mp;
  uy=k;
  y=0;
  jfe=90;
  ut=0;
  ye=1;
  mp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ye == y + 1;
  loop invariant jfe + ut == 90;
  loop invariant 0 <= jfe;
  loop invariant 0 <= ut;
  loop invariant 0 <= y;
  loop assigns jfe, mp, ut, y, ye;
*/
while (jfe>0&&y<uy) {
      if (jfe<=ye) {
          mp = jfe;
      }
      else {
          mp = ye;
      }
      ut = ut + mp;
      jfe = jfe - mp;
      y++;
      ye = ye + 1;
  }
}