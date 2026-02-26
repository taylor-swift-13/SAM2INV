int main1(int k,int n){
  int b, g, e, l;

  b=(n%8)+16;
  g=0;
  e=k;
  l=k;

  while (g<=b-1) {
      l = l+l;
      l = l+e;
      g = g+1;
  }

}
