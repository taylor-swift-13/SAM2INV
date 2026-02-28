int main1(int a,int n){
  int l, v, b;

  l=(n%36)+4;
  v=2;
  b=a;

  while (1) {
      b = b-b;
      if ((v%6)==0) {
          b = b+1;
      }
      v = v+1;
  }

}
