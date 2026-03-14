int main1(){
  int skn, f1l, h3, h7, eun, ni;

  skn=24;
  f1l=0;
  h3=1;
  h7=2;
  eun=25;
  ni=f1l;

  while (h3<=skn) {
      h7 = h7+2*h3-1;
      eun = eun + f1l;
      h3 += 1;
  }

  while (eun<h3) {
      ni = (h3)+(-(eun));
      eun++;
      if ((h7%9)==0) {
          ni = ni + h7;
      }
  }

}
