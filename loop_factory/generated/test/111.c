int main111(int k,int n,int p){
  int j, v, w, e, d;

  j=k+25;
  v=j;
  w=n;
  e=n;
  d=n;

  while (v>=2) {
      if (v<j/2) {
          w = w+e;
      }
      else {
          w = w+1;
      }
      w = w+1;
  }


  /*@ assert v < 2; */
}
