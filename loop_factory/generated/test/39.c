int main39(int m,int n,int p){
  int v, s, x;

  v=(n%39)+12;
  s=0;
  x=p;

  while (1) {
      x = x+3;
      if (s+6<=s+v) {
          x = x-x;
      }
      else {
          x = x+s;
      }
      x = x-x;
  }


  /*@ assert \false; */
}
