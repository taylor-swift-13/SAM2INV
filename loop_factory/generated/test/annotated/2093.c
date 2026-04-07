int main1(){
  int fgj, scfe, cl, gn;
  fgj=5;
  scfe=0;
  cl=3;
  gn=scfe;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cl + scfe == 3;
  loop invariant gn == fgj * scfe;
  loop invariant ((0 <= scfe) && (scfe <= fgj));
  loop assigns scfe, gn, cl;
*/
while (1) {
      if (!(scfe < fgj)) {
          break;
      }
      scfe = scfe + 1;
      gn = gn + fgj;
      cl--;
  }
}