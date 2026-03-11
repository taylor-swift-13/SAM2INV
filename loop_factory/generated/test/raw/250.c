int main1(){
  int fm, xrk, sr, q9x, m, f0o;

  fm=1+19;
  xrk=0;
  sr=0;
  q9x=fm;
  m=fm;
  f0o=0;

  while (1) {
      if (!(sr<=fm-1)) {
          break;
      }
      q9x = sr;
      m = m + xrk;
      sr++;
  }

  while (f0o-4>=0) {
      m = m+q9x*f0o;
      xrk = (xrk+fm)+(-(f0o));
      f0o = f0o + 1;
  }

}
