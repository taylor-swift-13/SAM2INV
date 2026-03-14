int main1(){
  int i, khm, vt, xcb;

  i=1+13;
  khm=0;
  vt=i;
  xcb=0;

  while (1) {
      if (!(khm<=i-1)) {
          break;
      }
      vt = i-khm;
      khm += 1;
      xcb += khm;
  }

  while (xcb<i) {
      vt = i-xcb;
      xcb += 2;
      vt += khm;
  }

}
