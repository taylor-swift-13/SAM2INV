int main1(int b,int n){
  int l, i, v;

  l=46;
  i=l;
  v=2;

  while (i>0) {
      if (i+7<=v+l) {
          v = v%8;
      }
      else {
          v = v*2;
      }
      i = i-1;
  }

}
