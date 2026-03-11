int main1(){
  int p6, c, f, d5cs, xph;

  p6=58;
  c=0;
  f=1;
  d5cs=0;
  xph=-1;

  while (f<=p6) {
      d5cs = d5cs+f*f;
      xph += p6;
      f = f + 1;
  }

  while (1) {
      c = c + 1;
      if (c>=d5cs) {
          break;
      }
  }

}
