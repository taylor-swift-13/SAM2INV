int main5(int k,int n,int q){
  int l, i, j, k1, v4, v3, v2;

  l=0;
  i=0;
  j=0;
  k1=0;
  v4=0;
  v3=0;
  v2=0;

  while (l<q) {
      if ((l%6)==0) {
          v2 = v2+1;
      }
      else {
          if ((l%5)==0) {
              v3 = v3+1;
          }
          else {
              if ((l%4)==0) {
                  v4 = v4+1;
              }
              else {
                  if ((l%3)==0) {
                      i = i+1;
                  }
                  else {
                      if ((l%2)==0) {
                          j = j+1;
                      }
                      else {
                          k1 = k1+1;
                      }
                  }
              }
          }
      }
      l = l+1;
  }

}
