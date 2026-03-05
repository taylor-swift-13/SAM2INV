int main61(int j){
  int p, u3, wzn, w1q, r;

  p=38;
  u3=p;
  wzn=13;
  w1q=5;
  r=14;

  while (wzn>0&&w1q>0&&r>0) {
      if (u3%3==0) {
          wzn--;
      }
      if (u3%3==1) {
          w1q = w1q - 1;
      }
      if (u3%3==2) {
          r--;
      }
      j = j + w1q;
      u3 = u3 + 1;
      j += 2;
  }

}
