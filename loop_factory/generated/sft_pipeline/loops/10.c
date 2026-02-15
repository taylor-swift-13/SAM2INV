int main10(int a,int m,int q){
  int l, i, j, k, v4, v3, v2, x, y, c, x1, y1, c1;

  l=0;
  i=0;
  j=0;
  k=0;
  v4=0;
  v3=0;
  v2=0;
  x=1;
  y=a;
  c=1;
  x1=a;
  y1=m;
  c1=0;

  while (l<m) {
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
                          k = k+1;
                      }
                  }
              }
          }
      }
      l = l+1;
  }

  while (c<q) {
      c = c+1;
      x = x*a+1;
      y = y*a;
  }

  while (x1!=0&&y1!=0) {
      if (x1>y1) {
          x1 = x1-y1;
      }
      else {
          y1 = y1-x1;
      }
  }

  while (c1<18) {
      q = q+8;
      m = m+8;
      c1 = c1+1;
  }

}
