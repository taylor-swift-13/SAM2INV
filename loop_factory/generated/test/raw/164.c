int main1(int i,int d){
  int lnb, hr, g, uio, q1;

  lnb=67;
  hr=0;
  g=28;
  uio=1;
  q1=0;

  while (g>0&&uio<=lnb) {
      if (!(g<=uio)) {
          g = 0;
      }
      else {
          g = g - uio;
      }
      uio = uio + 1;
      hr += 1;
      q1 = q1 + 1;
  }

}
