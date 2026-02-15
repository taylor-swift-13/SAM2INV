int main6(int a,int k,int p){
  int q, r, x;

  q=0;
  r=0;
  x=a;

  while (a>p*q+r) {
      if (r==p-1) {
          r = 0;
          q = q+1;
      }
      else {
          r = r+1;
      }
  }

  while (x>0) {
      x = x-1;
  }

}
