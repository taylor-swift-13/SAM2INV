int main1(int a,int p){
  int m, k, s;

  m=a+4;
  k=0;
  s=a;

  while (k<m) {
      s = s+4;
      s = s+s;
      if (k+4<=p+m) {
          s = s-s;
      }
      else {
          s = s+1;
      }
  }

}
