int main1(int e,int p){
  int ea, dvp, u15;

  ea=8;
  dvp=0;
  u15=0;

  while (dvp+4<=ea) {
      e = (ea-dvp)+(e);
      u15 -= 4;
      p = p+ea-dvp;
      ea = (dvp+4)-1;
  }

}
