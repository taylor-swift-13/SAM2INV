int main1(int m,int q){
  int l, i, v;

  l=m;
  i=l;
  v=-3;

  while (i>0) {
      if (m<v+1) {
          v = v+v;
      }
      else {
          v = m+m;
      }
      i = i/2;
  }

}
