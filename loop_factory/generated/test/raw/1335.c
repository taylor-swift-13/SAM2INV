int main1(){
  int q, tcg, um0, sk;

  q=1+12;
  tcg=(1%40)+2;
  um0=0;
  sk=20;

  while (tcg!=um0) {
      um0 = tcg;
      tcg = (tcg+q/tcg)/2;
      sk += tcg;
  }

}
