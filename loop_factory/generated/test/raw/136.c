int main1(int a,int b,int k,int m){
  int l, i, v, w;

  l=79;
  i=0;
  v=i;
  w=b;

  while (i<l) {
      w = w+w;
      w = w+v;
      if (v+3<l) {
          w = w+1;
      }
      i = i+1;
  }

}
