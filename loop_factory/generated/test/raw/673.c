int main1(){
  int wl, t3, lgl, popt, x, in4;

  wl=1;
  t3=wl;
  lgl=3;
  popt=-3;
  x=0;
  in4=t3;

  while (popt<wl) {
      x = x + t3;
      popt++;
      lgl++;
      in4 += 2;
  }

  while (popt+1<=lgl) {
      if (popt%2==0) {
          x = x + wl;
      }
      else {
          x = x+wl+1;
      }
      wl = wl + popt;
      lgl = ((popt+1))+(-(1));
  }

}
