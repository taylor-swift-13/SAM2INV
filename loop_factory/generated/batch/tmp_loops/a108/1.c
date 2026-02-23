int main1(int a,int k){
  int d, i, m, v;

  d=k;
  i=0;
  m=-4;
  v=a;

  while (i<d) {
      if (i<d/2) {
          m = m+v;
      }
      else {
          m = m+1;
      }
      m = m+v+v;
      m = m+1;
  }

}
