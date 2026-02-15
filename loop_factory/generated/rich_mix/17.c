int main17(int b,int m,int p){
  int x, y, q, r, l, i, j, k, v4, v3, v2, c, c1;

  x=b;
  y=m;
  q=0;
  r=0;
  l=0;
  i=0;
  j=0;
  k=0;
  v4=0;
  v3=0;
  v2=0;
  c=0;
  c1=0;

  while (x!=0&&y!=0) {
      if (x>y) {
          x = x-y;
      }
      else {
          y = y-x;
      }
  }

  while (m>b*q+r) {
      if (r==b-1) {
          r = 0;
          q = q+1;
      }
      else {
          r = r+1;
      }
  }

  while (l<b) {
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

  while (c<12) {
      m = m+1;
      b = b+1;
      c = c+1;
  }

  while (c1<1) {
      p = p+1;
      m = m+1;
      c1 = c1+1;
  }

}
