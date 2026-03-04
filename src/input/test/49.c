int main49(int a,int p,int q){
  int j, l, d;

  j=q;
  l=j+7;
  d=1;

  while (l>=j+1) {
      if (d==1) {
          d = 2;
      }
      else {
          if (d==2) {
              d = 1;
          }
      }
  }

}
