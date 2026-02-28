int main1(int m,int p){
  int n, v, c;

  n=49;
  v=0;
  c=p;

  while (v<n) {
      c = c+4;
      c = c-c;
      if (m<c+3) {
          c = c+v;
      }
  }

}
