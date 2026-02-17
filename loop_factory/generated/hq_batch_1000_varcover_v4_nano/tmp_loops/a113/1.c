int main1(int k,int n,int p,int q){
  int l, i, v;

  l=p;
  i=1;
  v=i;

  while (i<l) {
      v = v+v;
      if ((i%6)==0) {
          v = v+1;
      }
      else {
          v = v+v;
      }
      v = v+2;
      v = v+6;
      i = i*2;
  }

}
