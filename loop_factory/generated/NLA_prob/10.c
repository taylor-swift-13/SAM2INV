int main10(int a,int b,int q){
  int x, y;

  x=b;
  y=q;

  while (x!=0&&y!=0) {
      if (x>y) {
          x = x-y;
      }
      else {
          y = y-x;
      }
  }

}
