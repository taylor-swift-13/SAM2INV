int main1(int a,int n){
  int o, g, v;

  o=a+5;
  g=3;
  v=n;

  while (g<=o-1) {
      v = v+3;
      if (v+6<o) {
          v = v+1;
      }
      if (v+3<o) {
          v = v+v;
      }
  }

}
