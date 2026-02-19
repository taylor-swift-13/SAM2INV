int main1(int m,int n){
  int l, i, v;

  l=29;
  i=0;
  v=-3;

  while (i<l) {
      if ((i%8)==0) {
          v = v+1;
      }
      else {
          v = m-l;
      }
      i = i+1;
  }

}
