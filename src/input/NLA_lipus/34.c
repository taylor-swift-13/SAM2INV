/*@ requires a >= 1 && b >= 1;*/
int main1(){

  int x, y, u, v, a, b;
  
  x=a;
  y=b;
  u=b;
  v=0;

  while(x>y) {
    x=x-y;
    v=v+u;
  }
  /*@ assert x*u + y*v == a*b;*/
}

