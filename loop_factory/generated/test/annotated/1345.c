int main1(){
  int jp, et, mo, yb3, tw;
  jp=67;
  et=jp;
  mo=0;
  yb3=(1%28)+10;
  tw=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mo >= 0;
  loop invariant yb3 > 0;
  loop invariant yb3 == 11 - mo*(mo-1)/2;
  loop invariant tw == 11 + (jp - et) * mo;
  loop invariant et == jp;
  loop assigns yb3, tw, mo;
*/
while (1) {
      if (!(yb3>mo)) {
          break;
      }
      yb3 -= mo;
      tw = tw+jp-et;
      mo++;
  }
}