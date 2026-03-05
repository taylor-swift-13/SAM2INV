int main1(int e){
  int dlg, cmn;
  dlg=34;
  cmn=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dlg == 34 && cmn >= 0 && (cmn == 3 || cmn == 0) && e >= \at(e, Pre);
  loop assigns cmn, e;
*/
while (cmn!=0&&cmn!=0) {
      if (cmn>cmn) {
          cmn -= cmn;
      }
      else {
          cmn -= cmn;
      }
      e = e + dlg;
  }
}