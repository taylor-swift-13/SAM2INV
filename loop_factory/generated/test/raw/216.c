int main1(int a,int n){
  int l, i, v;

  l=41;
  i=0;
  v=-2;

  while (i<l) {
      if ((i%5)==0) {
          v = v*v;
      }
      else {
          v = v*v+v;
      }
      i = i+5;
  }

}
