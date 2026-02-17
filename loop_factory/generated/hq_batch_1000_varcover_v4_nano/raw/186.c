int main1(int b,int p,int q){
  int l, i, v;

  l=9;
  i=0;
  v=-1;

  while (i<l) {
      if ((i%4)==0) {
          v = v+v;
      }
      else {
          v = q+b;
      }
      i = i+1;
  }

}
