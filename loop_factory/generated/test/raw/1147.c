int main1(){
  int afog, wd, ny7, a, kto;

  afog=1;
  wd=afog;
  ny7=0;
  a=1;
  kto=(1%35)+8;

  while (kto>0) {
      a = a+kto*kto;
      wd = wd+ny7*ny7;
      ny7 = (kto*kto)+(ny7);
      wd = wd*4+5;
      kto -= 1;
  }

}
