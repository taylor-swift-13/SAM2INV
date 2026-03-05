int main1(int e,int l){
  int e1, j, be;

  e1=l;
  j=e1+3;
  be=-5;

  while (j>0) {
      be++;
      be = be+be*be;
      l = l*4+(be%2)+3;
  }

}
