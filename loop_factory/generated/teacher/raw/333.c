int main1(int k,int p){
  int d, i, v;

  d=p+3;
  i=2;
  v=-8;

  while (i+2<=d) {
      v = v+1;
      v = v+2;
      if (v+7<d) {
          v = v+1;
      }
      i = i+2;
  }

}
