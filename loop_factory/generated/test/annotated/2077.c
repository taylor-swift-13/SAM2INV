int main1(){
  int aud2, dbfp, ef, r;
  aud2=1+18;
  dbfp=0;
  ef=aud2;
  r=aud2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ef == aud2 - dbfp*dbfp;
  loop invariant r == aud2*(dbfp + 1);
  loop invariant dbfp >= 0;
  loop invariant ef >= 0;
  loop assigns ef, r, dbfp;
*/
while (ef >= (2*dbfp + 1)) {
      ef = (ef)+(-((2*dbfp + 1)));
      r += aud2;
      dbfp++;
  }
}