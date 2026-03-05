int main1(){
  int w7, nyit, ic;

  w7=1+10;
  nyit=1;
  ic=w7;

  while (nyit+2<=w7) {
      if (nyit<w7/2) {
          ic += ic;
      }
      else {
          ic = ic + 1;
      }
      ic += nyit;
  }

}
