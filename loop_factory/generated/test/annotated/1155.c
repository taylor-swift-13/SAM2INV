int main1(){
  int e3, sxv, gk, vw, tr;
  e3=(1%7)+6;
  sxv=1;
  gk=(1%40)+2;
  vw=0;
  tr=sxv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e3 == 7;
  loop invariant tr % 4 == 1;
  loop invariant gk * vw <= e3;
  loop invariant (2 <= gk && gk <= 3);
  loop invariant (0 <= vw && vw <= 3);
  loop assigns vw, gk, tr;
*/
while (gk!=vw) {
      vw = gk;
      gk = (gk+e3/gk)/2;
      tr += gk;
      tr = tr*4+5;
  }
}