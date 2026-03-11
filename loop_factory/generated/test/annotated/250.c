int main1(){
  int fm, xrk, sr, q9x, m, f0o;
  fm=1+19;
  xrk=0;
  sr=0;
  q9x=fm;
  m=fm;
  f0o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((sr == 0) ==> (q9x == fm)) &&
                   ((sr > 0) ==> (q9x == sr - 1));
  loop invariant xrk == 0;
  loop invariant (sr == 0) ==> (q9x == fm);
  loop invariant (sr > 0) ==> (q9x == sr - 1);
  loop invariant m == fm + sr * xrk;
  loop invariant 0 <= sr <= fm;
  loop assigns q9x, m, sr;
*/
while (1) {
      if (!(sr<=fm-1)) {
          break;
      }
      q9x = sr;
      m = m + xrk;
      sr++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == fm + q9x * ((f0o*(f0o - 1))/2);
  loop invariant xrk == (f0o*fm) - ((f0o*(f0o - 1))/2);
  loop invariant f0o >= 0;
  loop invariant q9x == fm - 1;
  loop assigns m, xrk, f0o;
*/
while (f0o-4>=0) {
      m = m+q9x*f0o;
      xrk = (xrk+fm)+(-(f0o));
      f0o = f0o + 1;
  }
}