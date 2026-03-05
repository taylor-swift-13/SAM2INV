int main1(){
  int q3, nby, dgz5, dtu8;

  q3=1;
  nby=0;
  dgz5=5;
  dtu8=0;

  while (nby<q3) {
      dtu8 = nby%5;
      if (nby>=dgz5) {
          dgz5 = (nby-dgz5)%5;
          dgz5 = dgz5+dtu8-dgz5;
      }
      else {
          dgz5 = dgz5 + dtu8;
      }
      nby += 1;
      dgz5 = dgz5 + 1;
  }

}
